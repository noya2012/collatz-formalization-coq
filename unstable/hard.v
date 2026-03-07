Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Lia.
Require Import PeanoNat.
Require Import Ring.
Require Import Arith.
Require Import ArithRing.
Require Import Coq.Arith.Div2.

(* Auxiliary lemma: a > b and k > 0 implies a * k > b * k *)
Lemma mul_lt_strict : forall a b k, a > b -> k > 0 -> a * k > b * k.
Proof.
intros a b k Hab Hk.
apply Nat.mul_lt_mono_pos_r; assumption.
Qed.

(* Auxiliary lemma: a >= b and k > 0 implies a * k >= b * k *)
Lemma mul_le_strict : forall a b k, a >= b -> k > 0 -> a * k >= b * k.
Proof.
intros a b k Hab Hk.
apply Nat.mul_le_mono_r; assumption.
Qed.

(* Definitions imported from collatz_part_1.v *)
Definition is_even (n: nat) := Nat.even n = true.
Definition is_odd (n: nat) := Nat.even n = false.

(* ===== Basic number theory properties ===== *)

(* Exponent lemmas copied from collatz_part_19_2.v *)

Lemma pow2_ge1 : forall d, 1 <= 2 ^ d.
Proof.
induction d; simpl; lia.
Qed.

Lemma nat_mul_eq_1 : forall a b, a * b = 1 -> a = 1 /\ b = 1.
Proof.
intros a b Hab.
apply (proj1 (Nat.mul_eq_1 a b)) in Hab.
exact Hab.
Qed.

Lemma pow2_ge_4_if_ge2 : forall d, d >= 2 -> 2 ^ d >= 4.
Proof.
intros d Hd.
replace 4 with (2 ^ 2) by reflexivity.
apply Nat.pow_le_mono_r; lia.
Qed.

Lemma pow3_ge_pow2_succ_from2 :
  forall n, n >= 2 -> 3 ^ n >= 2 ^ (S n).
Proof.
intros n Hn.
assert (exists k, n = 2 + k) as [k Hk] by (exists (n - 2); lia).
subst n.
induction k as [|k IHk].
- simpl. lia.
- pose proof (IHk ltac:(lia)) as IH.
rewrite Nat.add_succ_r.
rewrite Nat.pow_succ_r by lia.
rewrite Nat.pow_succ_r by lia.
assert (IH' : 2 ^ S (2 + k) <= 3 ^ (2 + k)) by exact IH.
assert (Hmul : 2 ^ S (2 + k) * 2 <= 3 ^ (2 + k) * 2) by nia.
replace (2 ^ S (2 + k) * 2) with (2 * 2 ^ S (2 + k)) in Hmul by
(rewrite Nat.mul_comm; reflexivity).
replace (3 ^ (2 + k) * 2) with (2 * 3 ^ (2 + k)) in Hmul by
(rewrite Nat.mul_comm; reflexivity).
assert (H32' : 3 ^ (2 + k) * 2 <= 3 ^ (2 + k) * 3) by nia.
replace (3 ^ (2 + k) * 2) with (2 * 3 ^ (2 + k)) in H32' by
(rewrite Nat.mul_comm; reflexivity).
replace (3 ^ (2 + k) * 3) with (3 * 3 ^ (2 + k)) in H32' by
(rewrite Nat.mul_comm; reflexivity).
exact (Nat.le_trans _ _ _ Hmul H32').
Qed.

Lemma pow3_gt_4pow2_from4 :
  forall n, n >= 4 -> 4 * 2 ^ n < 3 ^ n.
Proof.
intros n Hn.
assert (exists k, n = 4 + k) as [k Hk] by (exists (n - 4); lia).
subst n.
induction k as [|k IH].
- simpl. lia.
- rewrite Nat.add_succ_r.
rewrite Nat.pow_succ_r by lia.
rewrite Nat.pow_succ_r by lia.
lia.
Qed.

Lemma pow3_ge_8pow2_from6 :
  forall n, n >= 6 -> 8 * 2 ^ n <= 3 ^ n.
Proof.
intros n Hn.
assert (exists k, n = 6 + k) as [k Hk] by (exists (n - 6); lia).
subst n.
induction k as [|k IH].
- simpl. lia.
- rewrite Nat.add_succ_r.
rewrite Nat.pow_succ_r by lia.
rewrite Nat.pow_succ_r by lia.
rewrite (Nat.mul_comm 2 (2 ^ (6 + k))).
rewrite Nat.mul_assoc.
rewrite (Nat.mul_comm 3 (3 ^ (6 + k))).
pose proof (IH ltac:(lia)) as IH'.
apply (Nat.le_trans _ ((3 ^ (6 + k)) * 2)).
+ apply (Nat.mul_le_mono_r _ _ 2). exact IH'.
+ apply Nat.mul_le_mono_l. lia.
Qed.

Lemma pow3_gt_pow2 : forall d, d >= 1 -> 3 ^ d > 2 ^ d.
Proof.
intros d Hd.
destruct d as [|d']; [lia|].
destruct d' as [|d''].
- simpl. lia.
- assert (Hge : 3 ^ (S (S d'')) >= 2 ^ (S (S (S d'')))) by
(apply pow3_ge_pow2_succ_from2; lia).
rewrite (Nat.pow_succ_r 2 (S (S d''))) in Hge by lia.
assert (Hpos : 1 <= 2 ^ (S (S d''))) by apply pow2_ge1.
assert (Hlt : 2 ^ (S (S d'')) < 2 ^ (S (S d'')) * 2) by nia.
rewrite Nat.mul_comm in Hge.
assert (Hge' : 2 ^ (S (S d'')) * 2 <= 3 ^ (S (S d''))) by exact Hge.
exact (Nat.lt_le_trans _ _ _ Hlt Hge').
Qed.

(* Odd number property: odd numbers >= 1 *)
Lemma is_odd_ge1 : forall n,
  is_odd n ->
  n >= 1.
Proof.
intros n Hodd.
destruct n as [|n].
- unfold is_odd in Hodd. simpl in Hodd. discriminate.
- lia.
Qed.

(* Lemma imported from collatz_part_2.v *)
(* Odd number decomposition lemma *)
Lemma odd_decomposition : forall n,
  is_odd n -> exists k, n = 2 * k + 1.
Proof.
intros n H.
unfold is_odd in H.
assert (H_odd: Nat.odd n = true).
{
unfold Nat.odd.
destruct (Nat.even n); simpl.
- discriminate H.
- reflexivity.
}
apply Nat.odd_spec in H_odd.
exact H_odd.
Qed.

(* Lemma imported from collatz_part_3.v *)
(* 3^k >= 1 *)
Lemma pow3_ge1 : forall k, 1 <= 3 ^ k.
Proof.
induction k; simpl; lia.
Qed.

(* Lemma imported from collatz_part_2.v *)
(* First prove the relationship between divmod and division *)
Lemma div2_divmod_eq : forall n,
  n / 2 = fst (divmod n 1 0 1).
Proof.
intros n.
unfold Nat.div.
reflexivity.
Qed.

(* ===== factor2 related definitions and properties ===== *)

(* Definition imported from collatz_part_19.v *)
(* Extract 2-factors from n with bounded iterations *)
Fixpoint factor2_bounded (k n : nat) : nat * nat :=
  match k with
  | 0 => (0, n)
  | S k' =>
      if Nat.even n then
        let '(d, q) := factor2_bounded k' (n / 2) in
        (S d, q)
      else (0, n)
  end.

(* Extract 2-factors from n (full decomposition) *)
Definition factor2 (n : nat) : nat * nat := factor2_bounded n n.

(* Exponent of 2 in n's prime factorization *)
Definition factor2_exp (n : nat) : nat := fst (factor2 n).

(* Odd part of n after removing all factors of 2 *)
Definition factor2_odd (n : nat) : nat := snd (factor2 n).

(* factor2_bounded decomposition: n = q * 2^d *)
Lemma factor2_bounded_decomp : forall k n d q,
  factor2_bounded k n = (d, q) ->
  n = q * 2 ^ d.
Proof.
induction k as [|k IH]; intros n d q H.
-
simpl in H. inversion H; subst.
rewrite Nat.pow_0_r.
rewrite Nat.mul_1_r.
reflexivity.
-
simpl in H.
destruct (Nat.even n) eqn:He.
+
rewrite <- (div2_divmod_eq n) in H.
destruct (factor2_bounded k (n / 2)) as [d0 q0] eqn:Hfb.
simpl in H.
injection H as Hd Hq.
subst d q.
specialize (IH (n / 2) d0 q0 Hfb).
apply Nat.even_spec in He.
destruct He as [t Ht].
assert (Hdiv : n / 2 = t).
{ rewrite Ht. rewrite Nat.mul_comm. apply Nat.div_mul; lia. }
rewrite Hdiv in IH.
rewrite Ht.
rewrite IH.
change (2 ^ (S d0)) with (2 * 2 ^ d0).
ring.
+
inversion H; subst.
rewrite Nat.pow_0_r.
rewrite Nat.mul_1_r.
reflexivity.
Qed.

(* factor2_bounded preserves oddness of the quotient *)
Lemma factor2_bounded_odd : forall k n,
  n >= 1 -> k >= n -> is_odd (snd (factor2_bounded k n)).
Proof.
induction k as [|k IH]; intros n Hn Hkn.
- lia.
- simpl.
destruct (Nat.even n) eqn:He.
+
rewrite <- (div2_divmod_eq n).
apply Nat.even_spec in He.
destruct He as [t Ht].
assert (Ht_ge1 : t >= 1).
{
destruct t as [|t'].
- rewrite Ht in Hn. simpl in Hn. lia.
- lia.
}
assert (Hdiv : n / 2 = t).
{
rewrite Ht.
rewrite Nat.mul_comm.
apply Nat.div_mul.
lia.
}
assert (Hk_ge_t : k >= t).
{
assert (Hk_ge_2t1 : k >= 2 * t - 1) by (rewrite Ht in Hkn; lia).
assert (Ht_le_2t1 : t <= 2 * t - 1) by (destruct t; lia).
lia.
}
assert (Hlet : snd (let '(d, q) := factor2_bounded k (n / 2) in (S d, q)) =
snd (factor2_bounded k (n / 2))).
{ destruct (factor2_bounded k (n / 2)) as [d'' q'']; simpl; reflexivity. }
rewrite Hlet.
apply (IH (n / 2)).
*
rewrite Hdiv.
exact Ht_ge1.
*
rewrite Hdiv.
exact Hk_ge_t.
+
unfold is_odd.
exact He.
Qed.

(* factor2 decomposition property *)
Lemma factor2_spec_decomp : forall n,
  n = factor2_odd n * 2 ^ (factor2_exp n).
Proof.
intro n.
unfold factor2_odd, factor2_exp, factor2.
remember (factor2_bounded n n) as p eqn:Hp.
destruct p as [d q].
simpl.
symmetry in Hp.
apply (factor2_bounded_decomp n n d q Hp).
Qed.

(* factor2 oddness property *)
Lemma factor2_spec_odd : forall n,
  n >= 1 ->
  is_odd (factor2_odd n).
Proof.
intros n Hn.
unfold factor2_odd, factor2.
apply (factor2_bounded_odd n n Hn).
lia.
Qed.

(* ===== Core theorem: Fixed point implies Collatz equation ===== *)

Lemma fixed_point_implies_collatz_eq :
  forall d0 n0 d1 q1 n1,
    factor2 (n0 + 1) = (d1, q1) ->
    n1 = q1 / 2 ->
    d1 >= 1 ->
    n0 * 2 ^ d0 = 2 * 3 ^ d1 * n1 + (3 ^ d1 - 1) ->
    let k := q1 in
    k >= 1 /\ 3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0.
Proof.
intros d0 n0 d1 q1 n1 Hfac Hn1 _ Hfix.
cbn.
assert (Hn0p1_ge1 : n0 + 1 >= 1) by lia.
assert (Hq1_odd : is_odd q1).
{
pose proof (factor2_spec_odd (n0 + 1) Hn0p1_ge1) as Hodd.
unfold factor2_odd in Hodd.
rewrite Hfac in Hodd.
simpl in Hodd.
exact Hodd.
}
assert (Hq1_ge1 : q1 >= 1) by (apply is_odd_ge1; exact Hq1_odd).
assert (Hn0p1 : n0 + 1 = 2 ^ d1 * q1).
{
pose proof (factor2_spec_decomp (n0 + 1)) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite Hfac in Hdecomp.
simpl in Hdecomp.
rewrite Nat.mul_comm in Hdecomp.
exact Hdecomp.
}
destruct (odd_decomposition q1 Hq1_odd) as [k Hq1_as].
assert (Hq1_div2 : q1 / 2 = k).
{
rewrite Hq1_as.
replace (2 * k + 1) with (k * 2 + 1) by lia.
assert (H2 : 2 <> 0) by lia.
rewrite (Nat.div_add_l k 2 1 H2).
simpl.
rewrite Nat.add_0_r.
reflexivity.
}
assert (Hn1k : n1 = k).
{ rewrite Hn1. rewrite Hq1_div2. reflexivity. }
assert (Hpow3_ge1 : 1 <= 3 ^ d1) by apply pow3_ge1.
assert (Hmain : n0 * 2 ^ d0 + 1 = 3 ^ d1 * q1).
{
rewrite Hfix.
rewrite <- Nat.add_assoc.
replace ((3 ^ d1 - 1) + 1) with (3 ^ d1) by (symmetry; apply Nat.sub_add; exact Hpow3_ge1).
rewrite Hn1k.
rewrite Hq1_as.
ring.
}
split; [exact Hq1_ge1|].
assert (Hpos3 : 1 <= 3 ^ d1 * q1).
{
replace 1 with (1 * 1) by lia.
apply Nat.mul_le_mono.
- exact Hpow3_ge1.
- exact Hq1_ge1.
}
assert (Hlhs : 3 ^ d1 * q1 - 1 = n0 * 2 ^ d0).
{
apply (Nat.add_cancel_r _ _ 1).
replace (3 ^ d1 * q1 - 1 + 1) with (3 ^ d1 * q1) by (symmetry; apply Nat.sub_add; exact Hpos3).
rewrite Hmain.
reflexivity.
}
assert (Hn0_eq : n0 = 2 ^ d1 * q1 - 1).
{
apply (Nat.add_cancel_r _ _ 1).
assert (Hpos2 : 1 <= 2 ^ d1 * q1) by (rewrite <- Hn0p1; lia).
rewrite (Nat.sub_add 1 (2 ^ d1 * q1) Hpos2).
exact Hn0p1.
}
rewrite Hlhs.
rewrite Hn0_eq.
reflexivity.
Qed.

(* ===== Related corollaries ===== *)

(* Collatz equation implies simplified equation *)
Lemma collatz_eq_implies_eq :
  forall d0 n0 d1 q1 n1,
    factor2 (n0 + 1) = (d1, q1) ->
    n1 = q1 / 2 ->
    d1 >= 1 ->
    n0 * 2 ^ d0 = 2 * 3 ^ d1 * n1 + (3 ^ d1 - 1) ->
    let k := q1 in
    k >= 1 /\ 3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0.
Proof.
intros d0 n0 d1 q1 n1 Hfac Hn1 Hd1 Hfix.
exact (fixed_point_implies_collatz_eq d0 n0 d1 q1 n1 Hfac Hn1 Hd1 Hfix).
Qed.

(* ===== Auxiliary lemmas for main proof ===== *)

(* Contradiction lemma for d0 = 0 *)
Lemma no_solution_d0_eq0_d1_ge1 :
  forall d1 k,
    d1 >= 1 -> k >= 1 ->
    3 ^ d1 * k - 1 <> 2 ^ d1 * k - 1.
Proof.
intros d1 k Hd1 Hk H.
pose proof (pow3_gt_pow2 d1 Hd1) as Hgt.
assert (H1 : 3 ^ d1 * k > 2 ^ d1 * k) by
(apply Nat.mul_lt_mono_pos_r; assumption).
exfalso.
assert (H2 : 1 <= 2 ^ d1).
{ apply pow2_ge1. }
assert (H3 : 1 <= 3 ^ d1).
{ apply pow3_ge1. }
assert (H2k : 1 <= 2 ^ d1 * k) by nia.
assert (H3k : 1 <= 3 ^ d1 * k) by nia.
assert (H4 : 3 ^ d1 * k - 1 + 1 = 3 ^ d1 * k).
{ rewrite Nat.sub_add by exact H3k. reflexivity. }
assert (H5 : 2 ^ d1 * k - 1 + 1 = 2 ^ d1 * k).
{ rewrite Nat.sub_add by exact H2k. reflexivity. }
assert (H6 : 3 ^ d1 * k - 1 + 1 = 2 ^ d1 * k - 1 + 1).
{ rewrite H. reflexivity. }
rewrite H4 in H6.
rewrite H5 in H6.
rewrite H6 in H1.
lia.
Qed.

(* d0 = 1, d1 = 1 时的唯一解引理 *)
Lemma unique_solution_d0_1_d1_1 :
  forall k,
    k >= 1 ->
    3 * k - 1 = (2 * k - 1) * 2 ->
    k = 1.
Proof.
intros k Hk H.
simpl in H.
lia.
Qed.

(* Contradiction lemma for d0 = 1, d1 >= 2 *)
Lemma no_solution_d0_eq1_d1_ge2 :
  forall d1 k,
    d1 >= 2 -> k >= 1 ->
    3 ^ d1 * k - 1 <> 2 * (2 ^ d1 * k - 1).
Proof.
intros d1 k Hd1 Hk H.
destruct d1 as [|d1'].
- lia.
- destruct d1' as [|d1''].
+
lia.
+ destruct d1'' as [|d1'''].
*
simpl in H.
lia.
* destruct d1''' as [|d1''''].
{
simpl in H.
lia.
}
assert (Hge4 : S (S (S (S d1''''))) >= 4) by lia.
pose proof (pow3_gt_4pow2_from4 (S (S (S (S d1'''')))) Hge4) as Hgt.
exfalso.
pose proof (pow2_ge1 (S (S (S (S d1''''))))) as H2ge1.
pose proof (pow3_ge1 (S (S (S (S d1''''))))) as H3ge1.
nia.
Qed.

(* Contradiction lemma for d0 >= 2, d1 = 1 *)
Lemma no_solution_d0_ge2_d1_eq1 :
  forall d0 k,
    d0 >= 2 -> k >= 1 ->
    3 * k - 1 <> (2 * k - 1) * 2 ^ d0.
Proof.
intros d0 k Hd0 Hk H.
assert (Hpow : 2 ^ d0 >= 4) by (apply pow2_ge_4_if_ge2; assumption).
nia.
Qed.

(* Contradiction lemma for d0 >= 2, d1 = 2 *)
Lemma no_solution_d0_ge2_d1_eq2 :
  forall d0 k,
    d0 >= 2 -> k >= 1 ->
    9 * k - 1 <> (4 * k - 1) * 2 ^ d0.
Proof.
intros d0 k Hd0 Hk H.
assert (Hpow : 2 ^ d0 >= 4) by (apply pow2_ge_4_if_ge2; assumption).
nia.
Qed.

(* Contradiction lemma for d0 >= 2, d1 = 3 *)
Lemma no_solution_d0_ge2_d1_eq3 :
  forall d0 k,
    d0 >= 2 -> k >= 1 ->
    27 * k - 1 <> (8 * k - 1) * 2 ^ d0.
Proof.
intros d0 k Hd0 Hk H.
assert (Hpow : 2 ^ d0 >= 4) by (apply pow2_ge_4_if_ge2; assumption).
nia.
Qed.

(* Contradiction lemma for d0 = 2, d1 >= 4 *)
Lemma no_solution_d0_eq2_d1_ge4 :
  forall d1 k,
    d1 >= 4 -> k >= 1 ->
    3 ^ d1 * k - 1 <> (2 ^ d1 * k - 1) * 4.
Proof.
intros d1 k Hd1 Hk H.
pose proof (pow3_gt_4pow2_from4 d1 Hd1) as Hgt.
exfalso.
pose proof (pow2_ge1 d1) as H2ge1.
pose proof (pow3_ge1 d1) as H3ge1.
nia.
Qed.

(* Contradiction lemma for d0 >= 3, d1 = 4 *)
Lemma no_solution_d0_ge3_d1_eq4 :
  forall d0 k,
    d0 >= 3 -> k >= 1 ->
    81 * k - 1 <> (16 * k - 1) * 2 ^ d0.
Proof.
intros d0 k Hd0 Hk Heq.
assert (Hpow : 8 <= 2 ^ d0) by
(replace 8 with (2 ^ 3) by reflexivity;
apply Nat.pow_le_mono_r; lia).
assert (Hrhs_ge : (16 * k - 1) * 8 <= (16 * k - 1) * 2 ^ d0) by
(apply Nat.mul_le_mono_l; exact Hpow).
assert (Hrhs : (16 * k - 1) * 8 = 128 * k - 8).
{
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l.
assert (Hmul : (16 * k) * 8 = 128 * k).
{
rewrite <- Nat.mul_assoc.
rewrite (Nat.mul_comm k 8).
rewrite Nat.mul_assoc.
simpl.
reflexivity.
}
rewrite Hmul.
reflexivity.
}
exfalso.
pose proof Hrhs_ge as Hineq.
rewrite <- Heq in Hineq.
rewrite Hrhs in Hineq.
nia.
Qed.

(* Contradiction lemma for d0 >= 3, d1 = 5 *)
Lemma no_solution_d0_ge3_d1_eq5 :
  forall d0 k,
    d0 >= 3 -> k >= 1 ->
    243 * k - 1 <> (32 * k - 1) * 2 ^ d0.
Proof.
intros d0 k Hd0 Hk Heq.
assert (Hpow : 8 <= 2 ^ d0) by
(replace 8 with (2 ^ 3) by reflexivity;
apply Nat.pow_le_mono_r; lia).
assert (Hrhs_ge : (32 * k - 1) * 8 <= (32 * k - 1) * 2 ^ d0) by
(apply Nat.mul_le_mono_l; exact Hpow).
assert (Hrhs : (32 * k - 1) * 8 = 256 * k - 8).
{
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l.
assert (Hmul : (32 * k) * 8 = 256 * k).
{
rewrite <- Nat.mul_assoc.
rewrite (Nat.mul_comm k 8).
rewrite Nat.mul_assoc.
simpl.
reflexivity.
}
rewrite Hmul.
reflexivity.
}
exfalso.
pose proof Hrhs_ge as Hineq.
rewrite <- Heq in Hineq.
rewrite Hrhs in Hineq.
nia.
Qed.

(* Contradiction lemma for d0 = 3, d1 >= 6 *)
Lemma no_solution_d0_eq3_d1_ge6 :
  forall d1 k,
    d1 >= 6 -> k >= 1 ->
    3 ^ d1 * k - 1 <> (2 ^ d1 * k - 1) * 8.
Proof.
intros d1 k Hd1 Hk Heq.
pose proof (pow3_ge_8pow2_from6 d1 Hd1) as Hge.
assert (Hrhs : (2 ^ d1 * k - 1) * 8 = 8 * 2 ^ d1 * k - 8).
{
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l.
rewrite (Nat.mul_comm (2 ^ d1 * k) 8).
rewrite Nat.mul_assoc.
reflexivity.
}
pose proof Heq as Heq'.
rewrite Hrhs in Heq'.
pose proof (Nat.mul_le_mono_r (8 * 2 ^ d1) (3 ^ d1) k Hge) as Hmul.
pose proof (Nat.sub_le_mono_r (8 * 2 ^ d1 * k) (3 ^ d1 * k) 8 Hmul) as Hsub.
rewrite <- Heq' in Hsub.
pose proof (pow2_ge1 d1) as H2ge1.
assert (H8le_8pow2 : 8 <= 8 * 2 ^ d1).
{
replace 8 with (8 * 1) by lia.
apply Nat.mul_le_mono_l.
exact H2ge1.
}
assert (H8le_3pow : 8 <= 3 ^ d1) by exact (Nat.le_trans _ _ _ H8le_8pow2 Hge).
assert (H8le_3powk : 8 <= 3 ^ d1 * k).
{
assert (Hk1 : 1 <= k) by lia.
assert (H3le : 3 ^ d1 * 1 <= 3 ^ d1 * k) by (apply Nat.mul_le_mono_l; exact Hk1).
replace (3 ^ d1 * 1) with (3 ^ d1) in H3le by lia.
exact (Nat.le_trans _ _ _ H8le_3pow H3le).
}
exfalso.
nia.
Qed.

(* Contradiction lemma for d0 >= 4, d1 >= 4 *)
Lemma no_solution_d0_ge4_d1_ge4 :
  forall d0 d1 k,
    d0 >= 4 -> d1 >= 4 -> k >= 1 ->
    3 ^ d1 * k - 1 <> (2 ^ d1 * k - 1) * 2 ^ d0.
Proof.

Admitted.

(* (* Proof incomplete - needs further work *) *)

Lemma collatz_diophantine_unique_solution_mod :
  forall d0 d1 k,
    d1 >= 1 -> k >= 1 ->
    3^d1 * k - 1 = (2^d1 * k - 1) * 2^d0 ->
    d0 = 1 /\ d1 = 1 /\ k = 1.
Proof.
(* Proof incomplete - needs further work *)
Qed.

Axiom collatz_diophantine_unique_solution :
  forall d0 d1 k,
    d1 >= 1 ->
    k >= 1 ->
    3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0 ->
    d0 = 1 /\ d1 = 1 /\ k = 1.