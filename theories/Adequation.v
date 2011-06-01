Require Import Cnf.

Module Type ADEQUATION (Import F : CNF).
  Parameter vars : Type.
  Parameter interp : vars -> formula -> Prop.

  Parameter canonical_model : vars -> Sem.model.

  Axiom adequation :
    forall (v:vars) (f: formula), interp v f -> 
      Sem.sat_goal (canonical_model v) (F.make f).
End ADEQUATION.