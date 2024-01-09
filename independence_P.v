(**************************************************************************)
(* This is part of independence, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*           Na Zhang, Luoping Cui, Dakai Guo, and Wensheng Yu            *)
(**************************************************************************)

(** independence *)

Inductive Formula : Type:=
  | X : nat -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula.

Notation "¬ q" := (Not q)(at level 5,right associativity).
Notation "p → q" := (Contain p q)(at level 8,right associativity).
(* Notation " p ∨ q " := (¬p → q)(at level 7, right associativity).
Notation " p ∧ q " := (¬(p → ¬q))(at level 6, right associativity).
Notation " p ↔ q " := ((p → q)∧(q → p))(at level 9, right associativity). *)

Definition P1 (P: Formula -> Prop) := forall p q, P (p → (q → p)).
Definition P2 (P: Formula -> Prop) := 
  forall p q r, P ((p → (q → r)) → ((p → q) → (p → r))).
Definition P3 (P: Formula -> Prop) := forall p q, P ((¬p → q) → (¬p → ¬q) → p).

(* 公理P1是独立的 *)
(* P1的独立性: P2和P3以及原有的推理规则组成的一个推理系统，不能推出P1 *)

Inductive deduce_PA : Formula -> Prop :=
 | P2A : forall p q r, deduce_PA ((p → (q → r)) → ((p → q) → (p → r)))
 | P3A : forall p q, deduce_PA ((¬p → q) → (¬p → ¬q) → p)
 | MPA : forall p q, deduce_PA (p → q) -> deduce_PA p -> deduce_PA q.

Inductive v :=
  | zero
  | one
  | two.

Definition Not_v (p:v): v :=
  match p with
  | zero => one
  | one => zero
  | two => zero
  end.

Definition Contain_v (p q:v): v :=
  match p with
  | zero => match q with
            | zero => zero
            | one => one
            | two => one
            end
  | one => zero
  | two => match q with
            | zero => zero
            | one => one
            | two => one
            end
  end.

Fixpoint assi_v1 (p : Formula) : v :=
  match p with
  | X _ => two
  | ¬q => Not_v (assi_v1 q)
  | q → r => Contain_v (assi_v1 q) (assi_v1 r)
  end.

Definition quality_A (p :Formula) := assi_v1 p = zero.

(* P2具有性质A *)
Definition P2_A : forall p q r, 
  quality_A ((p → (q → r)) → ((p → q) → (p → r))).
Proof.
  intros. unfold quality_A. simpl. unfold Contain_v. 
  remember (assi_v1 p) as p1; remember (assi_v1 q) as q1; 
  remember (assi_v1 r) as r1. 
  destruct p1,q1,r1; auto.
Qed.

(* P3具有性质A *)
Example P3_A : forall p q, quality_A ((¬p → q) → (¬p → ¬q) → p).
Proof.
  intros. unfold quality_A. simpl. unfold Contain_v.
  destruct (assi_v1 p); destruct (assi_v1 q); simpl; auto.
Qed.

(* MP具有性质A *)
Example MP_A : forall p q,
  quality_A (p → q) -> quality_A p -> quality_A q.
Proof.
  intros. unfold quality_A.
  assert (assi_v1 (p → q) = zero -> (assi_v1 p = one \/ assi_v1 q = zero)).
  { intros. right. simpl in H1. rewrite -> H0 in H1. simpl in H1.
    remember (assi_v1 q). destruct v0. auto. apply H1. inversion H1. }
  apply H1 in H. destruct H. rewrite -> H0 in H. inversion H. apply H.
Qed.

(* P1(p → (q → p))中有一个公式没有性质A *)
Proposition P1_NA : forall p,
  assi_v1 p = two -> ~quality_A (p → (p → p)).
Proof.
  intros. intro. unfold quality_A in H0. simpl in H0. rewrite H in H0.
  unfold Contain_v in H0. inversion H0.
Qed.

Proposition PA_zero : forall p, deduce_PA p -> assi_v1 p = zero.
Proof.
  intros.
  induction H.
  apply P2_A.
  apply P3_A.
  eapply MP_A; eauto.
Qed.

Proposition P1_Independence : ~ P1 deduce_PA.
Proof.
  intro.
  pose proof PA_zero.
  pose proof P1_NA.
  assert (assi_v1 (X 0) = two). simpl; auto.
  apply H1 in H2. destruct H2. apply H0, H.
Qed.


(* 公理P2是独立的 *)
(* P2的独立性: P1和P3以及原有的推理规则组成的一个推理系统，不能推出P2 *)
Inductive deduce_PB : Formula -> Prop :=
 | P1B : forall p q , deduce_PB (p → (q → p))
 | P3B : forall p q, deduce_PB ((¬p → q) → (¬p → ¬q) → p)
 | MPB : forall p q, deduce_PB (p → q) -> deduce_PB p -> deduce_PB q.

Definition Contain_v2 (p q:v): v :=
  match p with
  | zero => match q with
          | zero => zero
          | one => one
          | two => one
          end
  | one => zero
  | two => match q with
          | zero => zero
          | one => zero
          | two => one
          end
  end.

Fixpoint assi_v2 (p : Formula) : v :=
  match p with
  | X _ => two
  | ¬q => Not_v (assi_v2 q)
  | q → r => Contain_v2 (assi_v2 q) (assi_v2 r)
  end.

Definition quality_B (p : Formula) := assi_v2 p = zero.

(* P1具有性质B *)
Example P1_B : forall p q, quality_B (p → (q → p)).
Proof.
  intros. unfold quality_B. simpl. unfold Contain_v2. destruct (assi_v2 p);
  destruct (assi_v2 q); auto.
Qed.

(* P3具有性质B *)
Example P3_B : forall p q, quality_B ((¬p → q) → (¬p → ¬q) → p).
Proof.
  intros. unfold quality_B. simpl. unfold Contain_v2.
  destruct (assi_v2 p); destruct (assi_v2 q); auto.
Qed.

(* MP具有性质B *) 
Example MP_B : forall p q,
  quality_B (p → q) -> quality_B p -> quality_B q.
Proof.
  intros.
  assert (assi_v2 (p → q) = zero -> (assi_v2 p = one \/ assi_v2 q = zero)).
  { intros. right. simpl in H1. rewrite -> H0 in H1. simpl in H1. 
    remember (assi_v2 q). destruct v0. auto. apply H1. inversion H1. }
  apply H1 in H. destruct H. rewrite -> H0 in H. inversion H. apply H.
Qed.

(* P2((p → (q → r)) → ((p → q) → (p → r)))中有一个公式没有性质B *)
Proposition P2_NB : forall p q, assi_v2 p = two -> assi_v2 q = one
  -> ~quality_B ((p → (q → p)) → ((p → q) → (p → p))).
Proof.
  intros. intro. unfold quality_B in H1. simpl in H1. 
  rewrite -> H in H1. rewrite -> H0 in H1. 
  unfold Contain_v in H1. inversion H1.
Qed.

Proposition PB_zero : forall p, deduce_PB p -> assi_v2 p = zero.
Proof.
  intros.
  induction H.
  apply P1_B.
  apply P3_B.
  eapply MP_B; eauto.
Qed.

Proposition P2_Independence : ~ P2 deduce_PB.
Proof.
  intro.
  pose proof PB_zero.
  pose proof P2_NB.
  assert (assi_v2 (X 0) = two). simpl; auto.
  assert (assi_v2 ((X 0) → (X 0)) = one). simpl; auto.
  pose proof H1 _ _ H2 H3.
  assert (deduce_PB (((X 0) → ((X 0) → (X 0)) → (X 0)) → 
    ((X 0) → (X 0) → (X 0)) → (X 0) → (X 0))).
  apply H. apply H0 in H5. destruct H4. unfold quality_B. auto.
Qed.
(* 5----------------------------------------------------------------------- *)

(* 定理2.5.18 公理P3是独立的 *)
(* P3的独立性: P1和P2以及原有的推理规则组成的一个推理系统，不能推出P3 *)

Inductive deduce_PC : Formula -> Prop :=
 | P1C : forall p q , deduce_PC (p → (q → p))
 | P2C : forall p q r, deduce_PC ((p → (q → r)) → ((p → q) → (p → r)))
 | MPC : forall p q, deduce_PC (p → q) -> deduce_PC p -> deduce_PC q.

Inductive v' := 
  | zero'
  | one'.

Definition Contain_v3 (p q:v'): v' :=
  match p with
  | zero' => match q with
          | zero' => zero'
          | one' => one'
          end
  | one' => zero'
  end.

Fixpoint assi_v3 (p : Formula) : v' :=
  match p with
  | X _ => one'
  | ¬q => zero'
  | q → r => Contain_v3 (assi_v3 q) (assi_v3 r)
  end.

Definition quality_C (p : Formula) := assi_v3 p = zero'.

(* P1具有性质C *)
Example P1_C : forall p q, quality_C (p → (q → p)).
Proof.
  intros. unfold quality_C. simpl. unfold Contain_v3. destruct (assi_v3 p);
  destruct (assi_v3 q); auto.
Qed.

(* P2具有性质C *)
Example P2_C : forall p q r, quality_C ((p → (q → r)) → ((p → q) → (p → r))).
Proof.
  intros. unfold quality_C. simpl. unfold Contain_v3.
  destruct (assi_v3 p); destruct (assi_v3 q); destruct (assi_v3 r); auto.
Qed.

(* MP具有性质C *)
Example MP_C : forall p q,
  quality_C (p → q) -> quality_C p -> quality_C q.
Proof.
  intros. unfold quality_C in *. simpl in H. rewrite -> H0 in H. 
  unfold Contain_v3 in H.
  rewrite <- H. destruct (assi_v3 q); auto.
Qed.

(* P3((¬p → q) → (¬p → ¬q) → p)中有一个公式没有性质C *)
Proposition P3_NC : forall p q, assi_v3 p = one' -> assi_v3 q = zero'
  -> ~quality_C ((¬p → q) → (¬p → ¬q) → p).
Proof.
  intros. intro. unfold quality_C in H1. simpl in H1.
  rewrite -> H in H1. rewrite -> H0 in H1. simpl in H1. inversion H1.
Qed.

Proposition PC_zero : forall p, deduce_PC p -> assi_v3 p = zero'.
Proof.
  intros.
  induction H.
  apply P1_C.
  apply P2_C.
  eapply MP_C; eauto.
Qed.

Proposition P3_Independence : ~ P3 deduce_PC.
Proof.
  intro.
  pose proof PC_zero.
  pose proof P3_NC.
  assert (assi_v3 (X 0) = one'). simpl; auto.
  assert (assi_v3 (¬(X 0)) = zero'). simpl; auto.
  pose proof H1 _ _ H2 H3.
  assert (deduce_PC ((¬ (X 0) → ¬ (X 0)) → (¬ (X 0) → ¬ ¬ (X 0)) → (X 0))).
  apply H. apply H0 in H5. destruct H4. unfold quality_C. auto.
Qed.


(* 公理系统的独立性 *)
Theorem P_Independence : (~ P1 deduce_PA) /\ (~ P2 deduce_PB)
  /\(~ P3 deduce_PC).
Proof.
  repeat split.
  apply P1_Independence.
  apply P2_Independence.
  apply P3_Independence.
Qed.
