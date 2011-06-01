(** This file collects a number of helper lemmas that are used
   throughout the development. 
   They are mainly double negations of logical equivalences that
   only hold in classical logic.
*)

Require Export Setoid.

Fact dnc : forall A, ~~(A \/ ~A).
Proof. intuition. Qed.
  
Fact double_not : forall R, ~~(~~R <-> R).
Proof. 
  intros R N; apply (dnc R); intro HR; apply N; intuition.
Qed.
Fact not_and_or_not : forall R1 R2, ~~(~(R1 /\ R2) <-> ~R1 \/ ~R2).
Proof. 
  intros R1 R2 N; apply (dnc R1); intro HR1; apply N; intuition.
Qed.
Fact not_or_and_not : forall R1 R2, ~~(~(R1 \/ R2) <-> ~R1 /\ ~R2).
Proof.
  intros R1 R2 N; apply (dnc R1); intro HR1; apply N; intuition.
Qed.

Fact dnc_and : forall R1 R2, ~~((~R1 \/ ~R2) \/ (R1 /\ R2)).
Proof. 
  intros; intuition.
Qed.
Fact dnc_or : forall R1 R2, ~~((~R1 /\ ~R2) \/ (R1 \/ R2)).
Proof. 
  intros; intuition.
Qed.
  
Fact or_distr_and : 
  forall R1 R2 R3, R1 \/ (R2 /\ R3) <-> (R1 \/ R2) /\ (R1 \/ R3).
Proof. intuition. Qed.
Fact or_and_distr : 
  forall R1 R2 R3, (R2 /\ R3) \/ R1 <-> (R1 \/ R2) /\ (R1 \/ R3).
Proof. intuition. Qed.
      
Ltac crewrite R N := rewrite R in N; clear R.
Fact imp_def : forall (A B : Prop), ~~((A -> B) <-> (~A \/ B)).
Proof. 
  intros A B N; apply (dnc A); intro HA; apply N; intuition.
Qed.
Fact nimp_def : forall (A B : Prop), ~~(~(A -> B) <-> (A /\ ~B)).
Proof. 
  intros A B N; apply (dnc A); intro HA; apply N; intuition.
Qed.

Fact iff_def : forall (A B : Prop),
  ~~((A <-> B) <-> (~A /\ ~B) \/ (A /\ B)).
Proof.
  intros A B N; unfold iff at 2 in N.
  apply (imp_def A B); intro R; crewrite R N.
  apply (imp_def B A); intro R; crewrite R N.
  tauto.
Qed.
Fact niff_def : forall (A B : Prop), 
  ~~(~(A <-> B) <-> ((A \/ B) /\ (~A \/ ~B))).
Proof.
  intros A B N; unfold iff at 2 in N.
  apply (not_and_or_not (A -> B) (B -> A)); intro R; crewrite R N.
  apply (imp_def A B); intro R; crewrite R N.
  apply (imp_def B A); intro R; crewrite R N.
  apply (not_or_and_not (~A) B); intro R; crewrite R N.
  apply (not_or_and_not (~B) A); intro R; crewrite R N.
  apply (double_not A); intro R; crewrite R N.
  apply (double_not B); intro R; crewrite R N.
  rewrite or_distr_and in N.
  do 2 rewrite or_and_distr in N.
  apply N; clear N; intuition.
Qed.

Fact iff_def2 : forall (A B : Prop),
  ~~((A <-> B) <-> (A \/ ~B) /\ (~A \/ B)).
Proof.
  tauto.
Qed.
Fact niff_def2 : forall (A B : Prop), 
  ~~(~(A <-> B) <-> ((A /\ ~B) \/ (~A /\ B))).
Proof.
  tauto.
Qed.