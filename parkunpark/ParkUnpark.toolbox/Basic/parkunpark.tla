----------------------------- MODULE parkunpark -----------------------------
EXTENDS TLC

CONSTANT
    Proc,                   \* Unpark Processes
    IDLE, NOTIFY, SLEEP,    \* Park state
    FREE, LOCKED            \* Mutex state

(***************************************************************************

\* Implementation of default_park from tokio-threadpool 0.1.5
--algorithm ParkUnpark {
    variables state = IDLE, mx = FREE, cv = 0;

    \* Single process which is parking on state. 
    fair process (Parker = "parker")
    variables old;
    {
        park_start: while (TRUE) {
            park_precheck:
            \* Check to see if the state is already NOTIFY,
            \* so we can just drop out without sleeping.
            assert state \in { IDLE, NOTIFY };
            if (state = NOTIFY) {
                state := IDLE;
                goto park_continue;
            };
            
            \* (Don't bother about timeout)
            
            \* We're going to sleep; take the lock
            park_lock: await mx = FREE; mx := LOCKED;
            
            park_sleep:
            
            assert state \in { IDLE, NOTIFY };
            old := state;

            \* If we're still idle then we can go into sleep state
            if (state = IDLE) {
                state := SLEEP
            };
            
            assert state \in { NOTIFY, SLEEP };
            
            \* Otherwise if we got notified we don't need to sleep
            if (old = NOTIFY) {
                park_setidle: \* Setting idle is a simple store
                state := IDLE;
                goto park_unlock;
            };
                        
            \* Release the lock and wait for the cv
            park_sleep_release: assert mx = LOCKED; mx := FREE;
            park_sleeping: await cv = 1;

            \* Retake the lock
            park_resume:
            await mx = FREE; mx := LOCKED; cv := 0;
            
            \* Set state to idle with a simple store
            park_setidle2: state := IDLE;
            
            \* Release the lock - XXX check we're holding the lock?
            park_unlock: assert mx = LOCKED; mx := FREE;
            
            \* We're on our way again
            park_continue: skip;
        }
    }
    
    \* multiple processes which can unpark the parker
    fair process (Unparker \in Proc)
    variables old;
    {
        unpark_start: while (TRUE) {
            unpark_precheck:
            \* If the state doesn't need waking (ie not SLEEP) then we can just set
            \* NOTIFY and we're done
            old := state;
            if (state = IDLE) { state := NOTIFY };
            if (old \in { IDLE, NOTIFY }) { goto unpark_start; };
            
            \* Parker is sleeping, we need the lock
            unpark_lock: await mx = FREE; mx := LOCKED;
            
            \* Swap in NOTIFY
            old := state || state := NOTIFY;

            \* If it isn't sleeping any more, we're done
            unpark_checkwake:
            if (old \in {IDLE, NOTIFY}) {
                goto unpark_unlock;
            };
            
            \* wake the sleeper
            unpark_wake: cv := 1;
            
            \* release the lock
            unpark_unlock: mx := FREE;
        }
    }
    
    process (Invariants = "invariants")
    {
        inv_start:
            either assert state \in { IDLE, NOTIFY, SLEEP };
            or assert mx \in { FREE, LOCKED };
            or assert cv \in { 0, 1 };
   
    }
}

***************************************************************************)
\* BEGIN TRANSLATION
\* Process variable old of process Parker at line 16 col 15 changed to old_
CONSTANT defaultInitValue
VARIABLES state, mx, cv, pc, old_, old

vars == << state, mx, cv, pc, old_, old >>

ProcSet == {"parker"} \cup (Proc) \cup {"invariants"}

Init == (* Global variables *)
        /\ state = IDLE
        /\ mx = FREE
        /\ cv = 0
        (* Process Parker *)
        /\ old_ = defaultInitValue
        (* Process Unparker *)
        /\ old = [self \in Proc |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = "parker" -> "park_start"
                                        [] self \in Proc -> "unpark_start"
                                        [] self = "invariants" -> "inv_start"]

park_start == /\ pc["parker"] = "park_start"
              /\ pc' = [pc EXCEPT !["parker"] = "park_precheck"]
              /\ UNCHANGED << state, mx, cv, old_, old >>

park_precheck == /\ pc["parker"] = "park_precheck"
                 /\ Assert(state \in { IDLE, NOTIFY }, 
                           "Failure of assertion at line 22, column 13.")
                 /\ IF state = NOTIFY
                       THEN /\ state' = IDLE
                            /\ pc' = [pc EXCEPT !["parker"] = "park_continue"]
                       ELSE /\ pc' = [pc EXCEPT !["parker"] = "park_lock"]
                            /\ state' = state
                 /\ UNCHANGED << mx, cv, old_, old >>

park_lock == /\ pc["parker"] = "park_lock"
             /\ mx = FREE
             /\ mx' = LOCKED
             /\ pc' = [pc EXCEPT !["parker"] = "park_sleep"]
             /\ UNCHANGED << state, cv, old_, old >>

park_sleep == /\ pc["parker"] = "park_sleep"
              /\ Assert(state \in { IDLE, NOTIFY }, 
                        "Failure of assertion at line 35, column 13.")
              /\ old_' = state
              /\ IF state = IDLE
                    THEN /\ state' = SLEEP
                    ELSE /\ TRUE
                         /\ state' = state
              /\ Assert(state' \in { NOTIFY, SLEEP }, 
                        "Failure of assertion at line 43, column 13.")
              /\ IF old_' = NOTIFY
                    THEN /\ pc' = [pc EXCEPT !["parker"] = "park_setidle"]
                    ELSE /\ pc' = [pc EXCEPT !["parker"] = "park_sleep_release"]
              /\ UNCHANGED << mx, cv, old >>

park_setidle == /\ pc["parker"] = "park_setidle"
                /\ state' = IDLE
                /\ pc' = [pc EXCEPT !["parker"] = "park_unlock"]
                /\ UNCHANGED << mx, cv, old_, old >>

park_sleep_release == /\ pc["parker"] = "park_sleep_release"
                      /\ Assert(mx = LOCKED, 
                                "Failure of assertion at line 53, column 33.")
                      /\ mx' = FREE
                      /\ pc' = [pc EXCEPT !["parker"] = "park_sleeping"]
                      /\ UNCHANGED << state, cv, old_, old >>

park_sleeping == /\ pc["parker"] = "park_sleeping"
                 /\ cv = 1
                 /\ pc' = [pc EXCEPT !["parker"] = "park_resume"]
                 /\ UNCHANGED << state, mx, cv, old_, old >>

park_resume == /\ pc["parker"] = "park_resume"
               /\ mx = FREE
               /\ mx' = LOCKED
               /\ cv' = 0
               /\ pc' = [pc EXCEPT !["parker"] = "park_setidle2"]
               /\ UNCHANGED << state, old_, old >>

park_setidle2 == /\ pc["parker"] = "park_setidle2"
                 /\ state' = IDLE
                 /\ pc' = [pc EXCEPT !["parker"] = "park_unlock"]
                 /\ UNCHANGED << mx, cv, old_, old >>

park_unlock == /\ pc["parker"] = "park_unlock"
               /\ Assert(mx = LOCKED, 
                         "Failure of assertion at line 64, column 26.")
               /\ mx' = FREE
               /\ pc' = [pc EXCEPT !["parker"] = "park_continue"]
               /\ UNCHANGED << state, cv, old_, old >>

park_continue == /\ pc["parker"] = "park_continue"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT !["parker"] = "park_start"]
                 /\ UNCHANGED << state, mx, cv, old_, old >>

Parker == park_start \/ park_precheck \/ park_lock \/ park_sleep
             \/ park_setidle \/ park_sleep_release \/ park_sleeping
             \/ park_resume \/ park_setidle2 \/ park_unlock
             \/ park_continue

unpark_start(self) == /\ pc[self] = "unpark_start"
                      /\ pc' = [pc EXCEPT ![self] = "unpark_precheck"]
                      /\ UNCHANGED << state, mx, cv, old_, old >>

unpark_precheck(self) == /\ pc[self] = "unpark_precheck"
                         /\ old' = [old EXCEPT ![self] = state]
                         /\ IF state = IDLE
                               THEN /\ state' = NOTIFY
                               ELSE /\ TRUE
                                    /\ state' = state
                         /\ IF old'[self] \in { IDLE, NOTIFY }
                               THEN /\ pc' = [pc EXCEPT ![self] = "unpark_start"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "unpark_lock"]
                         /\ UNCHANGED << mx, cv, old_ >>

unpark_lock(self) == /\ pc[self] = "unpark_lock"
                     /\ mx = FREE
                     /\ mx' = LOCKED
                     /\ /\ old' = [old EXCEPT ![self] = state]
                        /\ state' = NOTIFY
                     /\ pc' = [pc EXCEPT ![self] = "unpark_checkwake"]
                     /\ UNCHANGED << cv, old_ >>

unpark_checkwake(self) == /\ pc[self] = "unpark_checkwake"
                          /\ IF old[self] \in {IDLE, NOTIFY}
                                THEN /\ pc' = [pc EXCEPT ![self] = "unpark_unlock"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "unpark_wake"]
                          /\ UNCHANGED << state, mx, cv, old_, old >>

unpark_wake(self) == /\ pc[self] = "unpark_wake"
                     /\ cv' = 1
                     /\ pc' = [pc EXCEPT ![self] = "unpark_unlock"]
                     /\ UNCHANGED << state, mx, old_, old >>

unpark_unlock(self) == /\ pc[self] = "unpark_unlock"
                       /\ mx' = FREE
                       /\ pc' = [pc EXCEPT ![self] = "unpark_start"]
                       /\ UNCHANGED << state, cv, old_, old >>

Unparker(self) == unpark_start(self) \/ unpark_precheck(self)
                     \/ unpark_lock(self) \/ unpark_checkwake(self)
                     \/ unpark_wake(self) \/ unpark_unlock(self)

inv_start == /\ pc["invariants"] = "inv_start"
             /\ \/ /\ Assert(state \in { IDLE, NOTIFY, SLEEP }, 
                             "Failure of assertion at line 106, column 20.")
                \/ /\ Assert(mx \in { FREE, LOCKED }, 
                             "Failure of assertion at line 107, column 16.")
                \/ /\ Assert(cv \in { 0, 1 }, 
                             "Failure of assertion at line 108, column 16.")
             /\ pc' = [pc EXCEPT !["invariants"] = "Done"]
             /\ UNCHANGED << state, mx, cv, old_, old >>

Invariants == inv_start

Next == Parker \/ Invariants
           \/ (\E self \in Proc: Unparker(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Parker)
        /\ \A self \in Proc : WF_vars(Unparker(self))

\* END TRANSLATION
    
=============================================================================
\* Modification History
\* Last modified Tue Aug 07 16:18:14 PDT 2018 by jsgf
\* Created Tue Aug 07 10:43:04 PDT 2018 by jsgf
