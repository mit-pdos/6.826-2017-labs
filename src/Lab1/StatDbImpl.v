Require Import POCS.
Require Import VariablesAPI.
Require Import StatDbAPI.

(** * An implementation of StatDB

   StatDB is built on top of the Variables API, which maintains two variables
   [VarCount] and [VarSum]. StatDB reads and writes these two variables using
   the API provided in the VarsAPI module. [VarCount] stores the number of
   integers that [VarSum] sums up. The mean is just [VarSum]/[VarCount].

  *)


Module StatDB (v : VarsAPI) <: StatDbAPI.

  Import ListNotations.

  Definition add (v : nat) : proc unit :=
    sum <- v.read VarSum;
    count <- v.read VarCount;
    _ <- v.write VarSum (sum + v);
    _ <- v.write VarCount (count + 1);
    Ret tt.

  (** ** Exercise : complete the implementation of mean *)
  Definition mean : proc (option nat) :=
    Ret None.

  Definition init' : proc InitResult :=
    _ <- v.write VarCount 0;
    _ <- v.write VarSum 0;
    Ret Initialized.

  Definition init := then_init v.init init'.

  Definition recover : proc unit :=
    v.recover.

  (** ** Exercise : complete the implementation of the abstraction function: *)
  Definition statdb_abstraction (vars_state : VariablesAPI.State) (statdb_state : StatDbAPI.State) : Prop :=
    True.

  Definition abstr : Abstraction StatDbAPI.State :=
    abstraction_compose
      v.abstr
      {| abstraction := statdb_abstraction |}.

  Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
  Proof. unfold statdb_abstraction; auto. Qed.

  (** ** Exercise : complete the proof for the following admitted examples *)
  Example abstr_2_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
  Proof.
    unfold statdb_abstraction; simpl.
  Admitted.

  Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
  Proof.
    unfold statdb_abstraction; simpl.
  Admitted.

  Theorem init_ok : init_abstraction init recover abstr inited.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.

    step_proc_basic; intros.
    exists tt.
    simpl; intuition idtac.

    step_proc_basic; intros.
    exists tt.
    simpl; intuition idtac.

    step_proc_basic; intros.
    eauto.

    simpl in *; intuition subst.
    exists nil.
    unfold statdb_abstraction, inited.
    intuition auto.
  Qed.

  (** ** Exercise : complete the proof of [add] *)
  Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Proof.
    unfold add.
    intros.

    apply spec_abstraction_compose; simpl.
  Admitted.

  (** ** Exercise : complete the proof of [mean] *)
  Theorem mean_ok : proc_spec mean_spec mean recover abstr.
  Proof.
    unfold mean.
    intros.

    apply spec_abstraction_compose; simpl.

  Admitted.


  Theorem recover_noop : rec_noop recover abstr no_crash.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc_basic; intros.
    eauto.

    destruct a; simpl in *.
    intuition.
    eauto.
  Qed.

End StatDB.


Require Import VariablesImpl.
Module StatDBImpl := StatDB Vars.
Print Assumptions StatDBImpl.abstr_2_nok.
Print Assumptions StatDBImpl.abstr_3_ok.
Print Assumptions StatDBImpl.add_ok.
Print Assumptions StatDBImpl.mean_ok.
