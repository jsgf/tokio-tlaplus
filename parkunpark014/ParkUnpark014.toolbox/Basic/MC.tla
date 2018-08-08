---- MODULE MC ----
EXTENDS parkunpark, TLC

\* CONSTANT definitions @modelParameterConstants:0Proc
const_1533755966258128000 == 
{"1","2","3"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1533755966258129000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1533755966258130000 ==
<>(\A p \in Proc: pc[p] = "unpark_precheck" ~> pc["parker"] = "park_continue")
----
=============================================================================
\* Modification History
\* Created Wed Aug 08 12:19:26 PDT 2018 by jsgf
