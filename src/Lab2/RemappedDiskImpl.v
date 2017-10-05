Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.


Module RemappedDisk (bd : BadBlockAPI) <: OneDiskAPI.

  Import ListNotations.

  Definition read (a : addr) : proc block :=
    bs <- bd.getBadBlock;
      if a == bs then
        len <- bd.size;
          r <- bd.read (len-1);
          Ret r
      else
        r <- bd.read a;
      Ret r.

  Definition write (a : addr) (b : block) : proc unit :=
      Ret tt.

  Definition size : proc nat :=
    len <- bd.size;
    Ret (len - 1).

  Definition init' : proc InitResult :=
    len <- bd.size;
    if len == 0 then
      Ret InitFailed
    else
      bs <- bd.getBadBlock;
      if (lt_dec bs len) then
        Ret Initialized
      else
        Ret InitFailed.

  Definition init := then_init bd.init init'.

  Definition recover: proc unit :=
    bd.recover.


  Inductive remapped_abstraction (bs_state : BadBlockAPI.State) (rd_disk : OneDiskAPI.State) : Prop :=
    | RemappedAbstraction :
      let bs_disk := stateDisk bs_state in
      let bs_addr := stateBadBlock bs_state in
      forall
        (* Fill in the rest of your abstraction here. *)
        (* Hint 0: Try to prove [read_ok] to discover what you need from this abstraction *)
        (* Hint 1: What should be true about the non-bad blocks?   Replace [True] with what needs to be true *)
        (Hgoodblocks : True)
        (* Hint 2: What should be true about the bad block? *)
        (Hbadblock : True)
        (* Hint 3: What if the bad block address is the last address? *)
        (Hbadlast : True)
        (* Hint 4: What if the bad block address is past the end of the disk? *)
        (* Hint 5: To refer to the contents of disk [d] at address [a], you can write [diskGet a] *)
        (* Hint 6: To refer to the size of disk [d], you can write [diskSize d] *)
        (Hsize : diskSize bs_disk = diskSize rd_disk + 1),
      remapped_abstraction bs_state rd_disk.

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.

  Example abst_1_ok : remapped_abstraction
                         (BadBlockAPI.mkState [block1;block0] 0) [block0].
  Proof.
    constructor; auto.
    Admitted.

  Example abst_2_ok : remapped_abstraction
                         (BadBlockAPI.mkState [block1;block0;block0] 0) [block0;block0].
  Proof.
    constructor; auto.
    Admitted.

  Example abst_3_ok : remapped_abstraction
                         (BadBlockAPI.mkState [block0;block0] 1) [block0].
  Proof.
    constructor; auto.
    Admitted.

  Example abst_4_nok : ~ remapped_abstraction
                         (BadBlockAPI.mkState [block0;block0] 5) [block0].
  Proof.
    intro.
    inversion H; simpl in *.
    Admitted.

  Example abst_5_nok : ~ remapped_abstraction
                         (BadBlockAPI.mkState [block1;block1] 0) [block0].
  Proof.
    intro.
    inversion H; simpl in *.
    Admitted.

  (* Due to how remapped_abstraction is defined (as an inductive), it cannot be
  unfolded. This tactic identifies abstraction relations in the hypotheses and
  breaks them apart with [inversion], and also does some cleanup. *)
  Ltac invert_abstraction :=
    match goal with
    | H : remapped_abstraction _ _ |- _ => inversion H; clear H; subst; subst_var
    end.

  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    step_proc.
    Admitted.


  Theorem read_ok : forall a, proc_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
  Proof.
    unfold read.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; intros.
    destruct a'; simpl in *; intuition idtac.

    destruct (a == r).
    Admitted.


  Theorem remapped_abstraction_diskUpd_remap : forall state s v,
    remapped_abstraction state s ->
    remapped_abstraction (mkState
      (diskUpd (stateDisk state) (diskSize (stateDisk state) - 1) v)
      (stateBadBlock state)) (diskUpd s (stateBadBlock state) v).
  Proof.
    Admitted.


  Theorem remapped_abstraction_diskUpd_noremap : forall state s a v,
    remapped_abstraction state s ->
    a <> diskSize (stateDisk state) - 1 ->
    a <> stateBadBlock state ->
    remapped_abstraction (mkState
      (diskUpd (stateDisk state) a v)
      (stateBadBlock state)) (diskUpd s a v).
  Proof.
    Admitted.

  Hint Resolve remapped_abstraction_diskUpd_remap.
  Hint Resolve remapped_abstraction_diskUpd_noremap.

  Theorem write_ok : forall a v, proc_spec (OneDiskAPI.write_spec a v) (write a v) recover abstr.
  Proof.
    unfold write.
    intros.

    apply spec_abstraction_compose; simpl.
    Admitted.

  Theorem size_ok : proc_spec OneDiskAPI.size_spec size recover abstr.
  Proof.
    unfold diskSize.
    intros.

    apply spec_abstraction_compose; simpl.

    step_proc.
    destruct a'; simpl in *; intuition (subst; eauto).
    Admitted.

  (* This proof proves that recovery corresponds to no_wipe. *)
  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; intros.
    eauto.

    destruct a; simpl in *.
    autounfold in *; intuition eauto.
    subst; eauto.
  Qed.

End RemappedDisk.


Require Import BadBlockImpl.
Module x := RemappedDisk BadBlockDisk.
Print Assumptions x.write_ok.
