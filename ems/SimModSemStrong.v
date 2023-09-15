Require Import Coqlib Algebra.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

Set Implicit Arguments.

Local Open Scope nat_scope.






Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.

  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (SyscallOut fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (SyscallOut fn varg rvs) >>= k_tgt)
  | sim_itree_syscall_in
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_src k_tgt rv
      (K: sim_itree _ _ RR true true w0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (SyscallIn rv) >>= k_src)
                 (st_tgt0, trigger (SyscallIn rv) >>= k_tgt)

  | sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)


  | sim_itree_pput
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src k_tgt
      st_src1 st_tgt1
      (K: sim_itree _ _ RR true true w0 (st_src1, k_src tt) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
        (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_pget
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src k_tgt
      (K: sim_itree _ _ RR true true w0 (st_src0, k_src st_src0) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)

  | sim_itree_progress
      i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
      (SRC: i_src0 = true)
      (TGT: i_tgt0 = true)
    :
      _sim_itree sim_itree RR true true w0 (st_src0, i_src) (st_tgt0, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src st_tgt: st_local) ret_src ret_tgt :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: RR ret_src ret_tgt >>).

  Lemma _sim_itree_ind2 (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (SyscallOut fn varg rvs) >>= k_src)
              (st_tgt0, trigger (SyscallOut fn varg rvs) >>= k_tgt))
        (SYSCALLIN: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            rv k_src k_tgt
            (K: sim_itree _ _ RR true true w0 (st_src0, k_src tt) (st_tgt0, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (SyscallIn rv) >>= k_src)
              (st_tgt0, trigger (SyscallIn rv) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:_sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt k_src
            st_tgt1 st_src1
            (K: sim_itree _ _ RR true true w0 (st_src1, k_src tt) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt k_src
            (K: sim_itree _ _ RR true true w0 (st_src0, k_src st_src0) (st_tgt0, k_tgt st_tgt0)) ,
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: _sim_itree sim_itree RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply SYSCALLIN; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUT; eauto. }
    { eapply PGET; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition sim_itree {R} o_src o_tgt w0: relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq R)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN using _sim_itree_ind2; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                paco8 _sim_itree bot8 _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (SyscallOut fn varg rvs) >>= k_src)
              (st_tgt0, trigger (SyscallOut fn varg rvs) >>= k_tgt))
        (SYSCALLIN: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            rv k_src k_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src tt) (st_tgt0, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (SyscallIn rv) >>= k_src)
              (st_tgt0, trigger (SyscallIn rv) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt k_src
            st_tgt1 st_src1
            (K: paco8 _sim_itree bot8 _ _ RR true true w0 (st_src1, k_src tt) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt k_src
            (K: paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src st_src0) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _sim_itree_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply SYSCALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply SYSCALLIN; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { pclearbot. eapply PPUT; eauto. }
    { pclearbot. eapply PGET; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_indC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_indC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                     (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (SyscallOut fn varg rvs) >>= k_src)
                     (st_tgt0, trigger (SyscallOut fn varg rvs) >>= k_tgt)
  | sim_itree_indC_syscall_in
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      rv k_src k_tgt
      (K: sim_itree _ _ RR true true w0 (st_src0, k_src tt) (st_tgt0, k_tgt tt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (SyscallIn rv) >>= k_src)
                     (st_tgt0, trigger (SyscallIn rv) >>= k_tgt)

  | sim_itree_indC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_indC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                     (st_tgt0, i_tgt)
  | sim_itree_indC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                     (st_tgt0, i_tgt)


  | sim_itree_indC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_indC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_indC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Take X) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 6; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR r g w st_src st_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; eauto.
  Qed.

  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. des. esplits; eauto. }
    { econs 7; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. }
    { econs 12; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 13; eauto. }
  Qed.

  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lflagC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1 <8= r2)
    :
      @lflagC r1 <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. des. esplits; eauto. }
    { econs 7; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. eapply rclo8_base; eauto. }
    { econs 12; eauto. eapply rclo8_base; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 13; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down R0 R1 RR r g w st_src st_tgt f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up R0 R1 RR w st_src st_tgt f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src st_tgt)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w st_src st_tgt => set P
    end.
    revert b b0 w st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify.
    { guclo sim_itree_indC_spec. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
    { gstep. econs 3; eauto. i. gbase. eapply CIH; eauto. }
    { gstep. econs 4; eauto. i. gbase. eapply CIH; eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. des. esplits; eauto. }
    { gstep. econs 11; eauto.  gbase. eapply CIH; et. }
    { gstep. econs 12; eauto.  gbase. eapply CIH; et. }
    { eapply sim_itree_flag_down. gfinal. right.
      eapply paco8_mon; eauto. ss.
    }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS false false w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <8= r2) (LEs: s1 <8= s2)
    :
      lbindR r1 s1 <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
  Proof.
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src0, i_src). remember(st_tgt0, i_tgt).
    revert st_src0 i_src st_tgt0 i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM using _sim_itree_ind2; i; clarify.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
      { ss. }
      { ss. }
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. eapply rclo8_clo_base. econs; eauto.
    + econs; eauto. eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

  Structure grespectful clo : Prop :=
    grespect_intro {
        grespect_mon: monotone8 clo;
        grespect_respect :
        forall l r
               (LE: l <8= r)
               (GF: l <8= @_sim_itree r),
          clo l <8= gpaco8 (_sim_itree) (cpn8 (_sim_itree)) bot8 (rclo8 (clo \9/ gupaco8 (_sim_itree) (cpn8 (_sim_itree))) r);
      }.

  Lemma grespect_uclo clo
    (RESPECT: grespectful clo)
    :
    clo <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    eapply grespect8_uclo; eauto with paco.
    econs.
    { eapply RESPECT. }
    i. hexploit grespect_respect.
    { eauto. }
    { eapply LE. }
    { eapply GF. }
    { eauto. }
    i. inv H. eapply rclo8_mon.
    { eauto. }
    i. ss. des; ss. eapply _paco8_unfold in PR0.
    2:{ ii. eapply sim_itree_mon; [eapply PR1|]. i. eapply rclo8_mon; eauto. }
    ss. eapply sim_itree_mon.
    { eapply PR0; eauto. }
    i. eapply rclo8_clo. right. econs.
    eapply rclo8_mon; eauto. i. inv PR2.
    { left. eapply paco8_mon; eauto. i. ss. des; ss.
      left. auto. }
    { des; ss. right. auto. }
  Qed.

  Variant tauNC
    (r: forall S0 S1 (SS: st_local -> st_local -> S0 -> S1 -> Prop),
        bool -> bool -> world -> (st_local * itree Es S0) -> (st_local * itree Es S1) -> Prop):
    forall S0 S1 (SS: st_local -> st_local -> S0 -> S1 -> Prop),
      bool -> bool -> world -> (st_local * itree Es S0) -> (st_local * itree Es S1) -> Prop :=
    | tauNC_intro
        f_src0 f_tgt0 R0 R1 (RR: st_local -> st_local -> R0 -> R1 -> Prop) itr_src1 itr_tgt1 itr_src0 itr_tgt0
        st_src0 st_tgt0 w0
        (SIM: r _ _ RR f_src0 f_tgt0 w0 (st_src0, itr_src1) (st_tgt0, itr_tgt1))
        n
        (LEFT: itr_src0 = tau^{n};; itr_src1)
        m
        (RIGHT: itr_tgt0 = tau^{m};; itr_tgt1)
      :
      tauNC r RR f_src0 f_tgt0 w0 (st_src0, itr_src0) (st_tgt0, itr_tgt0)
  .
  Hint Constructors tauNC: core.

  Lemma tauNC_mon
    r1 r2
    (LE: r1 <8= r2)
    :
    tauNC r1 <8= tauNC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.
  Hint Resolve tauNC_mon: paco.

  Lemma tauNC_spec: tauNC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply grespect_uclo; eauto with paco.
    econs; eauto with paco.
    ii. ss. inv PR0. simpl_depind. subst.
    revert m. induction n; i; ss.
    - induction m; i; ss.
      + gfinal. right. eapply GF in SIM. pfold. eapply sim_itree_mon; et. ii; ss. right. eapply rclo8_base; ss.
      + guclo sim_itree_indC_spec. econs; et. guclo lflagC_spec. econs; et.
    - guclo sim_itree_indC_spec. econs; et. guclo lflagC_spec. econs; et.
  Qed.

  Variant guttC (r: forall S0 S1 (SS: st_local -> st_local -> S0 -> S1 -> Prop),
        bool -> bool -> world -> (st_local * itree Es S0) -> (st_local * itree Es S1) -> Prop):
    forall S0 S1 (SS: st_local -> st_local -> S0 -> S1 -> Prop),
      bool -> bool -> world -> (st_local * itree Es S0) -> (st_local * itree Es S1) -> Prop :=
    | guttC_intro
        f_src0 f_tgt0 R0 R1 (RR: st_local -> st_local -> R0 -> R1 -> Prop) itr_src1 itr_tgt1 itr_src0 itr_tgt0
        st_src0 st_tgt0 w0
        (SIM: r _ _ RR f_src0 f_tgt0 w0 (st_src0, itr_src1) (st_tgt0, itr_tgt1))
        (LEFT: itr_src0 ≳ itr_src1)
        (RIGHT: itr_tgt0 ≳ itr_tgt1)
      (* (MON: postcond_mon RR) *)
      :
      guttC r RR f_src0 f_tgt0 w0 (st_src0, itr_src0) (st_tgt0, itr_tgt0)
  .
  Hint Constructors guttC: core.

  Lemma guttC_mon
    r1 r2
    (LE: r1 <8= r2)
    :
    guttC r1 <8= guttC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.
  Hint Resolve guttC_mon: paco.

  Lemma guttC_grespectful: grespectful guttC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. csc.
    eapply GF in SIM.
    rename x2 into RR. rename x3 into f_src. rename x4 into f_tgt. rename x5 into w0.
    revert_until SIM. revert itr_src0 itr_tgt0.
    remember (st_src0, itr_src1) as tmp; revert Heqtmp.
    remember (st_tgt0, itr_tgt1) as tmp0; revert Heqtmp0. revert itr_src1 itr_tgt1 st_src0 st_tgt0.
    induction SIM using _sim_itree_ind2; i; clarify; simpl_euttge.
    { guclo tauNC_spec. }
    { guclo tauNC_spec. econs; et.
      gstep. econs; eauto. i. subst. gbase. eapply rclo8_clo. left. econs; ss. eapply rclo8_base. eauto.
    }
    { guclo tauNC_spec. econs; et.
      gstep. econs; eauto. i. subst. gbase. eapply rclo8_clo. left. econs; ss. eapply rclo8_base. eauto.
    }
    { guclo tauNC_spec. econs; et.
      gstep. econs; eauto. i. subst. gbase. eapply rclo8_clo. left. econs; ss. eapply rclo8_base. eauto.
    }
    { guclo sim_itree_indC_spec. econs; et. }
    { guclo tauNC_spec. econs; et. 2: { instantiate (2:=0). ss. } guclo sim_itree_indC_spec. econs; et. }
    { guclo tauNC_spec. econs; et. 2: { instantiate (2:=0). ss. } guclo sim_itree_indC_spec. econs; et. i. eapply K; et. }
    { guclo sim_itree_indC_spec. econs; et. }
    { guclo tauNC_spec. econs; et. 2: { instantiate (2:=0). ss. } guclo sim_itree_indC_spec. econs; et. i. eapply K; et. }
    { guclo tauNC_spec. econs; et. 2: { instantiate (2:=0). ss. } guclo sim_itree_indC_spec. econs; et. }
    { guclo tauNC_spec. econs; et.
      gstep. econs; eauto. i. subst. gbase. eapply rclo8_clo. left. econs; ss. eapply rclo8_base. eauto.
    }
    { guclo tauNC_spec. econs; et.
      gstep. econs; eauto. i. subst. gbase. eapply rclo8_clo. left. econs; ss. eapply rclo8_base. eauto.
    }
    { gstep. econs; eauto. gbase. eapply rclo8_clo. eauto with paco. }
  Qed.

  Lemma guttC_spec: guttC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply grespect_uclo; eauto with paco. eapply guttC_grespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Ltac my_red_both := try (Red.prw IRed._red_gen 2 1 0); try (Red.prw IRed._red_gen 1 1 0).

Lemma self_sim_itree:
  forall {R} st itr,
    sim_itree (R:=R) (fun _ '(src, tgt) => src = tgt) top2 false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e; [destruct s|].
  { dependent destruction c. rewrite <- ! bind_trigger. gstep.
    eapply sim_itree_call; ss. ii. subst.
    eapply sim_itree_flag_down. gbase. auto.
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction p.
    { gstep. econs; et.
      eapply sim_itree_progress_flag. gbase. auto.
    }
    { gstep. econs; et.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo sim_itree_indC_spec. econs 9. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 7. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
Qed.

Theorem eutt_sim_itree: forall {R} (u: itree Es R) (t: itree Es R) (EUTT: u ≈ t) st0,
    sim_itree (fun (_ : ()) '(st_src, st_tgt) => st_src = st_tgt) top2 false false tt (st0, u) (st0, t).
Proof.
  i. ginit. revert_until R. gcofix CIH. i.
  punfold EUTT. red in EUTT.
  dependent induction EUTT; simpobs_all.
  - gstep; econs; eauto. rr. esplits; ss; et.
  - guclo sim_itree_indC_spec. econs; eauto.
    guclo sim_itree_indC_spec. econs; eauto.
    gstep. econs; eauto.
    gbase. eapply CIH. pclearbot. eauto.
  - rewrite <- ! bind_trigger.
    (*** TODO: Use REFL+ after rebasing on FreeSim ***)
    (* guclo lbindC_spec. econs; eauto. *)
    (* { gfinal. right. eapply paco8_mon. { eapply self_sim_itree. } ii; ss. } *)
    (* ii. rr in SIM. des; subst. des_u. *)
    destruct e; [destruct s|].
    { destruct c. gstep. econs; ss; eauto. i. subst.
      guclo lflagC_spec. econs; ss.
      gbase. eapply CIH. pclearbot. eauto.
    }
    { destruct p.
      - gstep. econs; eauto. guclo lflagC_spec. econs.
        { gbase. eapply CIH. pclearbot. eauto. }
        { ss. }
        { ss. }
      - gstep. econs; eauto. guclo lflagC_spec. econs.
        { gbase. eapply CIH. pclearbot. eauto. }
        { ss. }
        { ss. }
    }
    destruct e.
    { guclo sim_itree_indC_spec. econsr; eauto. guclo sim_itree_indC_spec. econs; eauto. esplits.
      gstep. econsr; eauto. gbase. eapply CIH. pclearbot. eauto. }
    { guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. esplits.
      gstep. econsr; eauto. gbase. eapply CIH. pclearbot. eauto. }
    { guclo sim_itree_indC_spec. econs; eauto. i.
      gstep. econsr; eauto. gbase. eapply CIH. pclearbot. eauto. }
    { guclo sim_itree_indC_spec. econs; eauto. i.
      gstep. econsr; eauto. gbase. eapply CIH. pclearbot. eauto. }
  - guclo sim_itree_indC_spec. econs; eauto. guclo lflagC_spec. econs; eauto.
  - guclo sim_itree_indC_spec. econs; eauto. guclo lflagC_spec. econs; eauto.
Qed.


(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Variable (ms_src ms_tgt: ModSem._t).

  Let W: Type := (Any.t) * (Any.t).
  Inductive _sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: forall fn f_src (FINDS: In (fn, f_src) ms_src.(ModSem.fnsems)),
                             exists f_tgt, <<FINDT: In (fn, f_tgt) ms_tgt.(ModSem.fnsems)>>
                                                    /\ <<SIM: sim_fsem wf le f_src f_tgt>>;
    sim_initial: exists w_init, wf w_init (ms_src.(ModSem.initial_st), ms_tgt.(ModSem.initial_st));
  }.

End SIMMODSEM.

Definition sim (ms_src ms_tgt: ModSem.t) :=
  match ms_src, ms_tgt with
  | mytt, mytt => True
  | just ms_src, just ms_tgt => _sim ms_src ms_tgt
  | _, _ => False
  end
.

Global Program Instance _sim_Reflexive: Reflexive _sim.
Next Obligation.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    ii; ss. esplits; et. ii; clarify. des_u. exploit self_sim_itree; et.
  - ss.
Qed.

Global Program Instance sim_Reflexive: Reflexive sim.
Next Obligation.
  destruct x as [ms|]; ss. refl.
Qed.

Require Import Red IRed.
Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).
Ltac ired_both := ired_l; ired_r.
Lemma compose_aux_left:
  forall
    R
  world0 (wf0: world0 -> Any.t * Any.t -> Prop) (le0: world0 -> world0 -> Prop) (le_PreOrder0: PreOrder le0)
  world1 (wf1: world1 -> Any.t * Any.t -> Prop) (le1: world1 -> world1 -> Prop) (le_PreOrder1: PreOrder le1)
  ,
    let le_both := fun '(u0, w0) '(u1, w1) => le0 u0 u1 /\ le1 w0 w1 in
    let wf_both := fun '(u0, w0) '(lrs0, lrt0) =>
                     exists ls0 rs0 lt0 rt0 : Any.t,
                       lrs0 = Any.pair ls0 rs0 /\ lrt0 = Any.pair lt0 rt0 /\ wf0 u0 (ls0, lt0) /\ wf1 w0 (rs0, rt0) in
    forall
      (le_both_PreOrder: PreOrder le_both)
      (sems semt: itree _ _) wl0 wr_begin wr0 sl0 sr0 tl0 tr0 fs ft
      (LE: le1 wr_begin wr0)
      (WF: wf1 wr0 (sr0, tr0))
      (SIM: sim_itree wf0 le0 fs ft wl0 (sl0, sems) (tl0, semt))
    ,
      sim_itree (R:=R)
        wf_both le_both fs ft (wl0, wr_begin) (Any.pair sl0 sr0, focus_left sems) (Any.pair tl0 tr0, focus_left semt)
.
Proof.
  ii. ginit. revert_until le_both_PreOrder. gcofix CIH.
  i.
  punfold SIM.
  remember (lift_rel wf0 le0 wl0 eq) as tmp.
  remember (sl0, sems) as tmp0.
  remember (tl0, semt) as tmp1.
  revert Heqtmp. revert Heqtmp0. revert Heqtmp1.
  revert semt. revert sems. revert tl0. revert sl0.
  induction SIM using _sim_itree_ind2; i; clarify; simpl_depind; ired_both.
  - gstep. econs 1; eauto. rr. rr in RET. des. subst. esplits; et.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    { rr. esplits; et. }
  - gstep. rename w0 into wl0. rename w into wl1. econs 2; eauto.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    i. ss. des_ifs. des. ss. des. subst. exploit K; et. intro T; des. pclearbot.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; [|et|et].
    { etrans; et. }
  - gstep. econs 3; eauto.
    i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et.
    specialize (K vret); pclearbot. et.
  - gstep. econs 4; eauto.
    i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et.
    pclearbot. et.

  - guclo sim_itree_indC_spec. econs 5; eauto.
  - guclo sim_itree_indC_spec. des. econs 6; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - guclo sim_itree_indC_spec. econs 7; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. econs 8; eauto.
  - guclo sim_itree_indC_spec. econs 9; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. des. econs 10; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - gstep. econs; eauto. ired_both.
    gstep. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et. pclearbot; et.
  - gstep. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et. pclearbot; et.
  - pclearbot. gstep. econs 13; eauto. gbase. eapply CIH; et.
Qed.

Lemma compose_aux_right:
  forall
    R
  world0 (wf0: world0 -> Any.t * Any.t -> Prop) (le0: world0 -> world0 -> Prop) (le_PreOrder0: PreOrder le0)
  world1 (wf1: world1 -> Any.t * Any.t -> Prop) (le1: world1 -> world1 -> Prop) (le_PreOrder1: PreOrder le1)
  ,
    let le_both := fun '(u0, w0) '(u1, w1) => le0 u0 u1 /\ le1 w0 w1 in
    let wf_both := fun '(u0, w0) '(lrs0, lrt0) =>
                     exists ls0 rs0 lt0 rt0 : Any.t,
                       lrs0 = Any.pair ls0 rs0 /\ lrt0 = Any.pair lt0 rt0 /\ wf0 u0 (ls0, lt0) /\ wf1 w0 (rs0, rt0) in
    forall
      (le_both_PreOrder: PreOrder le_both)
      (sems semt: itree _ _) wl0 wl_begin wr0 sl0 sr0 tl0 tr0 fs ft
      (LE: le0 wl_begin wl0)
      (WF: wf0 wl0 (sl0, tl0))
      (SIM: sim_itree wf1 le1 fs ft wr0 (sr0, sems) (tr0, semt))
    ,
      sim_itree (R:=R)
        wf_both le_both fs ft (wl_begin, wr0) (Any.pair sl0 sr0, focus_right sems) (Any.pair tl0 tr0, focus_right semt)
.
Proof.
  ii. ginit. revert_until le_both_PreOrder. gcofix CIH.
  i.
  punfold SIM.
  remember (lift_rel wf1 le1 wr0 eq) as tmp.
  remember (sr0, sems) as tmp0.
  remember (tr0, semt) as tmp1.
  revert Heqtmp. revert Heqtmp0. revert Heqtmp1.
  revert semt. revert sems. revert tr0. revert sr0.
  induction SIM using _sim_itree_ind2; i; clarify; simpl_depind; ired_both.
  - gstep. econs 1; eauto. rr. rr in RET. des. subst. esplits; et.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    { rr. esplits; et. }
  - gstep. rename w0 into wr0. rename w into wr1. econs 2; eauto.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    i. ss. des_ifs. des. ss. des. subst. exploit K; et. intro T; des. pclearbot.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; [|et|et].
    { etrans; et. }
  - gstep. econs 3; eauto.
    i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et.
    specialize (K vret); pclearbot. et.
  - gstep. econs 4; eauto.
    i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et.
    pclearbot. et.

  - guclo sim_itree_indC_spec. econs 5; eauto.
  - guclo sim_itree_indC_spec. des. econs 6; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - guclo sim_itree_indC_spec. econs 7; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.

  - guclo sim_itree_indC_spec. econs 8; eauto.
  - guclo sim_itree_indC_spec. econs 9; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. des. econs 10; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - gstep. econs; eauto. ired_both.
    gstep. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et. pclearbot; et.
  - gstep. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et. pclearbot; et.
  - pclearbot. gstep. econs 13; eauto. gbase. eapply CIH; et.
Qed.



Theorem compose
  md_src0 md_tgt0 md_src1 md_tgt1
  (SIM0: sim md_src0 md_tgt0)
  (SIM1: sim md_src1 md_tgt1)
  :
  <<SIM: sim (md_src0 ⊕ md_src1) (md_tgt0 ⊕ md_tgt1)>>
.
Proof.
  destruct md_src0 as [md_src0|]; ss.
  2: { des_ifs. upt. des_ifs; ss. }
  destruct md_tgt0 as [md_tgt0|]; ss.
  destruct md_src1 as [md_src1|]; ss.
  2: { des_ifs. upt. des_ifs; ss. }
  destruct md_tgt1 as [md_tgt1|]; ss.
  inv SIM0. des.
  inv SIM1. des.
  set(le_both := (fun '(u0, w0) '(u1, w1) => le u0 u1 /\ le0 w0 w1): (world * world0) -> (world * world0) -> Prop).
  set(wf_both := (fun '(u0, w0) '(lrs0, lrt0) => exists ls0 rs0 lt0 rt0, lrs0 = Any.pair ls0 rs0 /\ lrt0 = Any.pair lt0 rt0 /\
                                                                           wf u0 (ls0, lt0) /\ wf0 w0 (rs0, rt0))).
  assert(LEBOTH: PreOrder le_both).
  { econs; et.
    - ii. rr. des_ifs; split; try refl.
    - ii. rr. des_ifs; ss. des_ifs. des; ss. des. split; try etrans; et.
  }
  econs; et.
  2: { instantiate (1:=wf_both). esplits ;ss. r. instantiate (1:=(w_init, w_init0)). ss. esplits; ss. }
  i. ss. rewrite in_app_iff in FINDS. des.
  - rewrite in_map_iff in *. des. destruct x; ss. clarify.
    exploit sim_fnsems; et. intro T; des. esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. esplits; et. ss. }
    ii. subst. destruct w; ss. des; subst.
    { eapply compose_aux_left; ss; et. refl. }
  - rewrite in_map_iff in *. des. destruct x; ss. clarify.
    exploit sim_fnsems0; et. intro T; des. esplits; et.
    { rewrite in_app_iff. right. rewrite in_map_iff. esplits; et. ss. }
    ii. subst. destruct w; ss. des; subst.
    { eapply compose_aux_right; ss; et. refl. }
Qed.

Require Import SimGlobalIndex SimGlobalIndexFacts.
From Ordinal Require Import Ordinal.


(*** TODO: put in FreeSim side ***)
Section SAFE.
Variable E: Type -> Type.
Variant _simg_safe
          (simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    f_src' f_tgt'
    (LE: (f_src' <= f_src)%ord)
    (LE: (f_tgt' <= f_tgt)%ord)
    (SIM: RR f_src' f_tgt' r_src r_tgt)
  :
    _simg_safe simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    ktr_src0 ktr_tgt0 fn varg rvs o_src o_tgt
    (SIM: forall vret, simg _ _ RR o_src o_tgt (ktr_src0 vret) (ktr_tgt0 vret))
  :
    _simg_safe simg RR f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)

| simg_safe_syscall_in
    ktr_src0 ktr_tgt0 rv o_src o_tgt
    (SIM: simg _ _ RR o_src o_tgt (ktr_src0 tt) (ktr_tgt0 tt))
  :
    _simg_safe simg RR f_src f_tgt (trigger (SyscallIn rv) >>= ktr_src0) (trigger (SyscallIn rv) >>= ktr_tgt0)
| simg_safe_tauL
    itr_src0 itr_tgt0 o_src
    (TAUL: True)
    (SIM: simg _ _ RR o_src f_tgt itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    itr_src0 itr_tgt0 o_tgt
    (TAUR: True)
    (SIM: simg _ _ RR f_src o_tgt itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_safe_chooseR
    X itr_src0 ktr_tgt0 o_tgt
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src o_tgt itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_safe_takeL
    X ktr_src0 itr_tgt0 o_src
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR o_src f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)

| simg_safe_event
    X (e: E X)
    ktr_src0 ktr_tgt0 o_src o_tgt
    (SIM: forall vret, simg _ _ RR o_src o_tgt (ktr_src0 vret) (ktr_tgt0 vret))
  :
    _simg_safe simg RR f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0)

.

Lemma simg_safe_spec:
  _simg_safe <8= gupaco7 (@_simg E) (cpn7 (@_simg E)).
Proof.
  i. eapply simg_indC_spec. inv PR.
  { econs; eauto. }
  { econs; eauto. i. subst. eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. i; subst. eauto. }
Qed.

End SAFE.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
End TAC.
Import TAC.

Lemma adequacy_aux
  (world: Type)
  (wf: world -> Any.t * Any.t -> Prop)
  (le: world -> world -> Prop)
  `{PreOrder _ le}
  ms_src ms_tgt
  (SIM: forall fn f_src (FINDS: In (fn, f_src) ms_src.(ModSem.fnsems)),
                             exists f_tgt, <<FINDT: In (fn, f_tgt) ms_tgt.(ModSem.fnsems)>>
                                                    /\ <<SIM: sim_fsem wf le f_src f_tgt>>)
  w0 st_src st_tgt
  itr_src itr_tgt
  f_src f_tgt
  (SIMF: sim_itree wf le f_src f_tgt w0 (st_src, itr_src) (st_tgt, itr_tgt))
  :
  paco7 (_simg (E:=void1)) bot7 (p_state * Any.t)%type (p_state * Any.t)%type
    (fun _ _ '(st_src, ret_src) '(st_tgt, ret_tgt) =>
       lift_rel wf le w0 (@eq Any.t) st_src st_tgt ret_src ret_tgt) (Nat.b2n f_src) (Nat.b2n f_tgt)
    (interp_Es (ModSem.prog ms_src) itr_src st_src)
    (interp_Es (ModSem.prog ms_tgt) itr_tgt st_tgt)
.
Proof.
  ginit.
  revert_until SIM.
  gcofix CIH. i.
  {
    rr in SIMF.
    remember (st_src, itr_src).
    remember (st_tgt, itr_tgt).
    remember w0 in SIMF at 2.
    revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw.
    punfold SIMF. induction SIMF using _sim_itree_ind2; ss; i; clarify.
    - rr in RET. des. step; try refl. r. esplits; et.
    - steps. rename x into n. unfold assume, triggerUB. des_ifs; steps; ss. des. rename e into T.
      hexploit SIM; et.
      { eapply nth_error_In; et. }
      intro U; des.
      eapply In_nth_error in FINDT. des. rename n0 into m.
      force. exists m. steps. des_ifs; steps.
      2: { contradict n0. esplits; et. }
      clear e.
      steps. rewrite T, FINDT. ss. steps.
      gstep. econsr; et.
      { guclo bindC_spec. econs.
        { gbase. eapply CIH. { instantiate (1:=w1). eauto. } }
        { i. ss. des_ifs. r in SIM1. des. subst.
          hexploit K; et. i. des. pclearbot.
          steps. gbase. eapply CIH; ss.
          eapply sim_itree_bot_flag_up. eauto.
        }
      }
      { eapply Ord.S_is_S. }
      { eapply Ord.S_is_S. }
    - step. i. subst. gstep. econsr; et.
      { hexploit (K vret). i. des. pclearbot.
        steps. gbase. eapply CIH; et.
      }
      { eapply Ord.S_is_S. }
      { eapply Ord.S_is_S. }
    - step. i. subst. gstep. econsr; et.
      { pclearbot. steps. gbase. eapply CIH; et.
      }
      { eapply Ord.S_is_S. }
      { eapply Ord.S_is_S. }
    - ired_both. steps.
    - des. force. exists x. steps. eapply IH; eauto.
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - steps.
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - des. force. exists x. steps. eapply IH; eauto.
    - steps. gstep. econsr; et.
      { pclearbot. gbase; et. }
      { eapply Ord.S_is_S. }
      { eapply Ord.S_is_S. }
    - steps. gstep. econsr; et.
      { pclearbot. gbase; et. }
      { eapply Ord.S_is_S. }
      { eapply Ord.S_is_S. }
    - gstep. econsr; et.
      { gbase. eapply CIH; et. pclearbot. eauto. }
      { eapply Ord.S_is_S. }
      { eapply Ord.S_is_S. }
  }
Unshelve.
  all: try exact Ord.O.
  all: ss.
Qed.

Theorem _adequacy_whole
  `{EMSConfig}
  ms_src ms_tgt
  (SIM: ModSemPair._sim ms_src ms_tgt)
  :
  (Beh.of_program (ModSem.compile ms_tgt))
  <1=
    (Beh.of_program (ModSem.compile ms_src)).
Proof.
  eapply adequacy_global_itree2; ss.
  inv SIM.
  des. ginit.
  unfold ModSem.initial_itr, guarantee.
  unfold snd, base.fmap; ss. unfold fmap_itree, ITree.map. steps. unfold assume, triggerUB. des_ifs; steps; ss. des.
  hexploit sim_fnsems; et.
  { eapply nth_error_In; et. }
  intro U; des. eapply In_nth_error in FINDT. des. force. esplits; et. steps.
  des_ifs; steps; ss.
  2: { contradict n0. unshelve esplits; et. }
  clear e0.
  rewrite e, FINDT. ss. steps.
  guclo bindC_spec. econs.
  { gstep. econsr; et.
    { gfinal. right. eapply adequacy_aux; et. }
    { eapply Ord.S_is_S. }
    { eapply Ord.S_is_S. }
  }
  { i. des_ifs. r in SIM0. des; clarify. steps.
    { refl. }
    { refl. }
  }
Unshelve.
  all: try exact Ord.O.
Qed.

Theorem adequacy_whole
  ms_src ms_tgt
  (SIM: ModSemPair.sim ms_src ms_tgt)
  :
  ms_tgt ⊑B ms_src
.
Proof.
  i.
  destruct ms_src as [ms_src|]; ss.
  2: { des_ifs; ss. }
  destruct ms_tgt as [ms_tgt|]; ss.
  ii. eapply _adequacy_whole; et.
Qed.

Theorem adequacy
  ms_src ms_tgt
  (SIM: ModSemPair.sim ms_src ms_tgt)
  :
  ms_tgt ⊑ ms_src
.
Proof.
  ii. eapply adequacy_whole; et.
  eapply compose; et. refl.
Qed.

Theorem adequacy_unit
  ms_tgt
  :
  ms_tgt ⊑B ε
.
Proof.
  ii. ss. unfold ModSem.compile' in *. des_ifs; ss.
  - pfold. econsr; ss.
Qed.

End ModSemPair.
