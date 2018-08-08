---- MODULE MC ----
EXTENDS parkunpark, TLC

\* CONSTANT definitions @modelParameterConstants:0Proc
const_1533740902231124000 == 
{"1","2","3"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1533740902231125000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1533740902231126000 ==
<>(\A p \in Proc: pc[p] = "unpark_precheck" ~> pc["parker"] = "park_continue")
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1533740902231127000 ==
<>[](pc["parker"] = "park_sleep")
----
=============================================================================
\* Modification History
\* Created Wed Aug 08 08:08:22 PDT 2018 by jsgf
