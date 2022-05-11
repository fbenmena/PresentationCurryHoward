From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dessert : Set := pudding.
Inductive vide : Set := .

Definition PP := fun n => if n is 0 then dessert else nat.

Definition f1 := fun (n : nat) =>
  match n return (PP n) with
  | 0 => pudding
  | _ => n
  end.

Definition f2 : forall n : nat, PP n -> PP n.+1 := fun (n : nat) =>
   match n return (PP n -> PP n.+1) with
   | 0 => fun _ => 1
   | n'.+1 => fun _ => n'.+2
   end.

Definition f3 : (PP 0) -> (forall n : nat, PP n -> PP n.+1) -> forall n : nat, PP n :=
  fun (f : PP 0) (ff: forall n : nat, PP n -> PP n.+1) =>
    fix F (n : nat) : (PP n) :=
      match n return (PP n) with
      | 0 => f
      | n'.+1 => ff n' (F n')
      end.

Definition g1 : (forall n : nat, PP n -> PP n.+1) := fun (n : nat) (m : PP n) =>
  match n return (PP n -> _) with
  | 0 => fun _ => 1
  | n'.+1 => fun m => m + n.+1
  end m.

Definition somme := nat_rec PP pudding g1.

Lemma etape_heredite : forall n : nat, n + 0 = n -> n.+1 + 0 = n.+1.
Proof.
  move => n H.
  have Hyp : n.+1 + 0 = (n + 0).+1 => //.
  rewrite Hyp -[in RHS]H //.
Qed.

Lemma addition_0_neutre_a_droite: forall n : nat, n + 0 = n.
Proof nat_ind (fun n : nat => n + 0 = n) (erefl 0) etape_heredite.

Lemma lemme_addition_0_neutre_a_droite_bis : forall n : nat, n + 0 = n.
Proof.
  elim.
  by [].
  move => n HRec.
  have HypSuppl : n.+1 + 0 = (n + 0).+1.
    by [].
  rewrite HypSuppl -[in RHS]HRec.
  by [].
Qed.

Lemma lemme_addition_0_neutre_a_droite_ter : forall n : nat, n + 0 = n.
Proof.
  by elim => [//| n HRec]; rewrite -[in RHS]HRec addSn.
Qed.

Lemma lemme_addition_0_neutre_a_gauche : forall n : nat, 0 + n = n.
Proof.
  by [].
Qed.

Lemma lemme_transitivite_implication : forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move => P Q R H1 H2 p.
  exact: (H2 (H1 p)).
Qed.

Lemma lemme_tautologie_boolenne : forall b1 b2: bool, (b1 || b2) && b1 == b1.
Proof.
  move => b1 b2.
  case b1.
    by [].
  case b2.
    by [].
    by [].
Qed.

Lemma lemme_transitivite_implication_bis : forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move => P Q R H1 H2 p.
  apply: H2.
  apply: H1.
  by [].
Qed.

Lemma lemme_renversant_01 : forall p1 p2: nat, p1 <= 3 -> 4 <= p2 -> p1 * 4 <= 3 * p2.
Proof.
  move => p1 p2 H1 H2.
  apply: leq_mul.
  by [].
  by [].
Qed.

Lemma lemme_renversant_01_bis : forall p1 p2: nat, p1 <= 3 -> 4 <= p2 -> p1 * 4 <= 3 * p2.
Proof.
  move => p1 p2.
  apply: leq_mul.
Qed.

Lemma lemme_tautologie_boolenne_bis : forall b1 b2: bool, (b1 || b2) && b1 == b1.
Proof.
  move => b1 b2.
  elim: b1.
  by [].
  by elim b2.
Qed.

Lemma exo_01 : forall n1 n2 : nat, n1 + n2 = n2 + n1.
Proof.
Admitted.

Lemma exo_02 : forall n1 n2 m3: nat, n1 + n2 + n3 = n1 + (n2 + n3).
Proof.
Admitted.

Lemma exo_03 : forall n1 n2: nat, n1 + n2 + n3 = n1 + (n2 + n3).
Proof.
Admitted.

Lemma exo_04 : forall n1 : nat, n1 * 0 = 0.
Proof.
Admitted.

Lemma exo_05 : forall n1 n2 : nat, n1 * n2.+1 = n1 * n2 + n2.
Proof.
Admitted.

Lemma exo_06 : forall n1 n2 n3 : nat, n1 * (n2 + n3) = n1 * n2 + n1 * n3.
Proof.
Admitted.

Lemma exo_07 : forall n1 n2 : nat, n1 * n2 = n2 * n1.
Proof.
Admitted.

Lemma exo_08 : forall n1 n2 n3 : nat, (n1 + n2) * n3 = n1 * n3 + n2 * n3.
Proof.
Admitted.

Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
Admitted.

Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
Proof.
Admitted.

Lemma not_contrad :  ~(P /\ ~P).
Proof.
Admitted.

Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
Proof.
Admitted.

Lemma not_not_exm : ~ ~ (P \/ ~ P).
Proof.
Admitted.

Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
Admitted.

Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
Proof.
Admitted.

Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
Proof.
Admitted.

Lemma or_to_imp : P \/ Q -> ~ P -> Q.
Proof.
Admitted.

Lemma imp_to_not_not_or : (P -> Q) -> ~ ~(~P \/ Q).
Proof.
Admitted.

Section CompositionSurjectiviteEtInjectivite.
Variables (f g : nat -> nat).
Hypothesis gf_surjective : forall (c : nat), exists a:nat, g (f a) = c.
Hypothesis gf_injective : forall (x y : nat),  g (f x) = g (f y) -> x = y.

Lemma g_surjective : forall c : nat, exists b:nat, g b = c.
Proof.
Admitted.

Lemma f_injective : forall x y : nat, f x = f y -> x = y.
Proof.
Admitted.

Check g_surjective.
Check f_injective.
End CompositionSurjectiviteEtInjectivite.
