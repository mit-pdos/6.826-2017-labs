Require Import POCS.
Require Import AtomicPairAPI.
Require Import Common.OneDiskAPI.


Module AtomicPair (d : OneDiskAPI) <: AtomicPairAPI.

  (** To implement this API, we suggest you work out a way that does not use
      logging but instead maintains two sets of blocks and a pointer to switch
      between them. You can use [block0] and [block1] as concrete values for the
      pointer and [b == b'] to compare blocks in code. *)

  (* To make implementations more consistent, we recommend this layout (where
  the pointer is in address 0). *)
  Definition ptr_a : addr := 0.
  Definition data0a : addr := 1.
  Definition data1a : addr := 2.
  Definition data0b : addr := 3.
  Definition data1b : addr := 4.

  (* We plug some extra facts into the automation to make the above definitions
  more convenient. You can ignore these; they automatically make [auto] and
  [autorewrite with upd] more powerful. *)

  Ltac addr_omega :=
    progress unfold ptr_a, data0a, data1a, data0b, data1b;
    omega.

  Hint Extern 2 (_ <> _ :> addr) => addr_omega.
  Hint Extern 2 (_ < _) => addr_omega.

  Opaque diskGet.

  (* EXERCISE (3a): implement this procedure *)
  Definition get : proc (block*block) :=
  Ret (block0, block0).

  (* EXERCISE (3a): implement this procedure *)
  Definition put (p : block*block) : proc unit :=
  Ret tt.

  (* EXERCISE (3a): implement this procedure *)
  Definition init' : proc InitResult :=
    Ret InitFailed.

  Definition init := then_init d.init init'.

  (* Using this approach with a pointer (as opposed to write-ahead logging), you
  won't need a recovery procedure. *)
  Definition recover: proc unit :=
    d.recover.

  (* EXERCISE (3a): write an abstraction relation for your implementation *)
  Definition atomic_pair_abstraction (ds : OneDiskAPI.State) (ps : AtomicPairAPI.State) : Prop :=
  True.

  (* EXERCISE (3a): come up with some examples of disks and pairs that satisfy
     the abstraction relation and those that don't. Prove them correct.

     Come up with at least 3 positive examples and 3 negative examples. *)

  Definition abstr : Abstraction AtomicPairAPI.State :=
    abstraction_compose d.abstr {| abstraction := atomic_pair_abstraction |}.

  (* For this lab, we provide a notation for diskUpd. Not only can you use this
     to write [diskUpd d a b] as [d [a |-> b]] but you will also see this notation
     in goals. This should especially make it easier to read goals with many
     updates of the same disk.

     Remember that the code still uses diskUpd underneath, so the same theorems
     apply. We recommend using [autorewrite with upd] or [autorewrite with upd
     in *] in this lab to simplify diskGet/diskUpd expressions, rather than
     using the theorems manually. *)
  Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 31, left associativity).

  (* EXERCISE (3b): prove your initialization procedure correct. *)
  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
  Admitted.

  (* EXERCISE (3b): prove you can correctly get the pair using your abstraction
  relation. *)
  Theorem get_ok : proc_spec get_spec get recover abstr.
  Proof.
    unfold get.
    apply spec_abstraction_compose; simpl.
  Admitted.


  Lemma diskGet_eq_values : forall d a b b',
      diskGet d a ?|= eq b ->
      diskGet d a ?|= eq b' ->
      a < diskSize d ->
      b = b'.
  Proof.
  Admitted.

  (* We used this tactic to simplify goals with
   H1: diskGet d a ?|= eq b
   H2: diskGet d a ?|= eq b'

   The tactic proves b = b'.
   *)
  Ltac eq_values :=
    match goal with
    | [ H: diskGet ?d ?a ?|= eq ?b,
           H': diskGet ?d ?a ?|= eq ?b' |- _ ] =>
      assert (b = b') by (apply (@diskGet_eq_values d a b b'); auto);
      subst
    end.


  (* EXERCISE (3c): prove that the atomic update is correct.

   We highly recommend separating at least the crash cases into lemmas and
   proving them separately. *)
  Theorem put_ok : forall v, proc_spec (put_spec v) (put v) recover abstr.
  Proof.
    unfold put; intros.
    apply spec_abstraction_compose; simpl.
  Admitted.

  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; intros.
    eauto.

    destruct a; simpl in *.
    autounfold in *; intuition; subst; eauto.
  Qed.

End AtomicPair.
