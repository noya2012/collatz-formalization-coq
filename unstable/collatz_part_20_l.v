Load "collatz_part_20.v".

Local Open Scope nat.

(* Lemma: equation for fixed points of canonical macrostep *)
Lemma canonical_mod62_macrostep_end_fixed_point_equation :
  forall m0,
    m0 mod 6 = 2 ->
    canonical_mod62_macrostep_end m0 = m0 ->
    exists d0 n0 d1 q1 n1,
      factor2 m0 = (d0, n0) /\
      factor2 (n0 + 1) = (d1, q1) /\
      n1 = q1 / 2 /\
      d1 >= 1 /\
      n0 = valid_R1R0_entry_number d1 n1 /\
      m0 = n0 * 2 ^ d0 /\
      n0 * 2 ^ d0 = 2 * 3 ^ d1 * n1 + (3 ^ d1 - 1).
Proof.
intros m0 Hm0_mod6 Hfix.
destruct (canonical_mod62_macrostep_end_closed_form m0 Hm0_mod6)
as (d0 & n0 & d1 & q1 & n1 & Hp0 & Hp1 & Hn1 & Hd1 & Hn0 & Hr).
exists d0, n0, d1, q1, n1.
repeat split; try assumption.
- pose proof (factor2_spec_decomp m0) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite Hp0 in Hdecomp.
exact Hdecomp.
- pose proof (factor2_spec_decomp m0) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite Hp0 in Hdecomp.
rewrite Hfix in Hr.
rewrite Hdecomp in Hr.
exact Hr.
Qed.

(* Lemma: fixed point (macrostep) induces the diophantine equation parameters *)
Lemma canonical_mod62_macrostep_fixed_point_diophantine :
  forall m0,
    m0 mod 6 = 2 ->
    canonical_mod62_macrostep_end m0 = m0 ->
    exists d0 n0 d1 q1 n1,
      factor2 m0 = (d0, n0) /\
      factor2 (n0 + 1) = (d1, q1) /\
      n1 = q1 / 2 /\
      d1 >= 1 /\
      let k := q1 in
      k >= 1 /\ 3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0.
Proof.
intros m0 Hm0_mod6 Hfix.
destruct (canonical_mod62_macrostep_end_fixed_point_equation m0 Hm0_mod6 Hfix)
as (d0 & n0 & d1 & q1 & n1 & Hp0 & Hp1 & Hn1 & Hd1 & _Hn0 & _Hm0 & Hcollatz_eq).
exists d0, n0, d1, q1, n1.
split; [exact Hp0|].
split; [exact Hp1|].
split; [exact Hn1|].
split; [exact Hd1|].
exact (collatz_eq_implies_eq d0 n0 d1 q1 n1 Hp1 Hn1 Hd1 Hcollatz_eq).
Qed.

(* Reduction: macrostep fixed point uniqueness follows from diophantine uniqueness. *)
Lemma canonical_mod62_macrostep_fixed_point_unique_at_2_from_diophantine :
  (forall d0 d1 k,
      d1 >= 1 -> k >= 1 ->
      3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0 ->
      d0 = 1 /\ d1 = 1 /\ k = 1) ->
  forall m0,
    m0 mod 6 = 2 ->
    canonical_mod62_macrostep_end m0 = m0 ->
    m0 = 2.
Proof.
intros Huniq m0 Hm0_mod6 Hfix.
destruct (canonical_mod62_macrostep_fixed_point_diophantine m0 Hm0_mod6 Hfix)
as (d0 & n0 & d1 & q1 & n1 & Hp0 & Hp1 & _Hn1 & Hd1 & Hdioph).
cbv beta in Hdioph.
destruct Hdioph as [Hq1_ge1 Heq].
destruct (Huniq d0 d1 q1 Hd1 Hq1_ge1 Heq) as [Hd0_eq1 [Hd1_eq1 Hq1_eq1]].
subst d0 d1 q1.
assert (Hn0p1 : n0 + 1 = 1 * 2 ^ 1).
{
pose proof (factor2_spec_decomp (n0 + 1)) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite Hp1 in Hdecomp.
exact Hdecomp.
}
assert (Hn0 : n0 = 1).
{
assert (Hn0p1' : n0 + 1 = 2).
{ rewrite Hn0p1. simpl. lia. }
lia.
}
subst n0.
pose proof (factor2_spec_decomp m0) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite Hp0 in Hdecomp.
simpl in Hdecomp.
lia.
Qed.

(* Lemma: contribution sum for canonical macrostep chains *)
Lemma canonical_mod62_macrostep_contribution :
  forall m0 d0 n0,
    factor2 m0 = (d0, n0) ->
    sum_contributions (extract_simple_chains (canonical_mod62_macrostep_chains m0)) = d0 + 1.
Proof.
intros m0 d0 n0 Hf.
unfold canonical_mod62_macrostep_chains.
rewrite Hf.
remember (factor2 (n0 + 1)) as p1 eqn:Hp1.
destruct p1 as [d1 q1].
simpl.
lia.
Qed.
(* Lemma: lower bound on cycle contribution sum *)
Lemma canonical_mod62_cycle_contribution_lower_bound :
  forall t m0,
    canonical_mod62_cycle t m0 ->
    2 * t <=
      sum_contributions (extract_simple_chains (canonical_mod62_iterated_chains t m0)).
Proof.
intros t m0 Hcycle.
unfold canonical_mod62_cycle in Hcycle.
destruct Hcycle as [Ht_ge1 [Hm0_mod6 _]].
pose proof (mod62_macrostep_iterated_lower_bound_canonical t m0 Ht_ge1 Hm0_mod6) as H.
set (chains := canonical_mod62_iterated_chains t m0) in H.
set (mt := canonical_mod62_iterated_end t m0) in H.
destruct H as [_ [_ [_ [Hlb _]]]].
subst chains.
exact Hlb.
Qed.

(* Lemma: a canonical mod6=2 cycle implies strict R0 advantage, with linear lower bound *)
Lemma canonical_mod62_cycle_R0_advantage_strong :
  forall t m0,
    canonical_mod62_cycle t m0 ->
    let chains := canonical_mod62_iterated_chains t m0 in
    let total_seq :=
      concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
    fst (count_operations total_seq) > snd (count_operations total_seq) /\
    fst (count_operations total_seq) - snd (count_operations total_seq) =
      sum_contributions (extract_simple_chains chains) /\
    2 * t <= fst (count_operations total_seq) - snd (count_operations total_seq).
Proof.
intros t m0 Hcycle.
unfold canonical_mod62_cycle in Hcycle.
destruct Hcycle as [Ht_ge1 [Hm0_mod6 _]].
pose proof (mod62_macrostep_iterated_lower_bound_canonical t m0 Ht_ge1 Hm0_mod6) as H.
set (chains := canonical_mod62_iterated_chains t m0) in H.
set (mt := canonical_mod62_iterated_end t m0) in H.
destruct H as [_ [_ [_ [Hlb Hadv]]]].
unfold chains_R0_advantage in Hadv.
cbv beta in Hadv.
destruct Hadv as [Hgt Heq].
subst chains.
cbv beta.
split; [exact Hgt|].
split; [exact Heq|].
rewrite Heq.
exact Hlb.
Qed.

(* Lemma: total sequence length of macrostep chains at input 2 *)
Lemma canonical_mod62_macrostep_chains_2_total_seq_length :
  length
    (concat
       (map (fun '(b, d, _, _, _) => canonical_chain b d)
            (canonical_mod62_macrostep_chains 2))) = 6.
Proof.
simpl.
reflexivity.
Qed.

(* Lemma: contribution sum of macrostep chains at input 2 *)
Lemma canonical_mod62_macrostep_chains_2_contribution :
  sum_contributions (extract_simple_chains (canonical_mod62_macrostep_chains 2)) = 2.
Proof.
simpl.
lia.
Qed.

(* Lemma: total sequence length of iterated chains at input 2 *)
Lemma canonical_mod62_iterated_chains_2_total_seq_length :
  forall t,
    length
      (concat
         (map (fun '(b, d, _, _, _) => canonical_chain b d)
              (canonical_mod62_iterated_chains t 2))) = 6 * t.
Proof.
induction t as [|t IH].
- simpl. lia.
- cbn [canonical_mod62_iterated_chains].
cbv beta.
rewrite canonical_mod62_macrostep_end_2.
rewrite map_app, concat_app, app_length.
rewrite canonical_mod62_macrostep_chains_2_total_seq_length.
rewrite IH.
lia.
Qed.

(* Lemma: contribution sum of iterated chains at input 2 *)
Lemma canonical_mod62_iterated_chains_2_contribution :
  forall t,
    sum_contributions (extract_simple_chains (canonical_mod62_iterated_chains t 2)) = 2 * t.
Proof.
induction t as [|t IH].
- simpl. lia.
- cbn [canonical_mod62_iterated_chains].
cbv beta.
rewrite canonical_mod62_macrostep_end_2.
rewrite extract_simple_chains_app, sum_contributions_app.
rewrite canonical_mod62_macrostep_chains_2_contribution.
rewrite IH.
lia.
Qed.

(* A provable special case (the known cycle at 2). *)
Corollary canonical_mod62_cycle_length_upper_bound_at_2 :
  forall t,
    let chains := canonical_mod62_iterated_chains t 2 in
    let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
    length total_seq <= 3 * t + 2 * sum_contributions (extract_simple_chains chains).
Proof.
intros t.
set (chains := canonical_mod62_iterated_chains t 2).
set (total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains)).
change (length total_seq <= 3 * t + 2 * sum_contributions (extract_simple_chains chains)).
subst total_seq chains.
rewrite (canonical_mod62_iterated_chains_2_total_seq_length t).
rewrite (canonical_mod62_iterated_chains_2_contribution t).
lia.
Qed.

(* ================================================================ *)
(*  Route 1 continuation: R1R0 / operation-count equivalences       *)
(*  (moved from collatz_part_21.v)                                  *)
(* ================================================================ *)

Local Open Scope nat.

(* Lemma: factor2 of an odd number returns (0, n) *)
Lemma factor2_of_odd :
  forall n,
    is_odd n ->
    factor2 n = (0, n).
Proof.
intros n Hodd.
unfold factor2.
destruct n as [|n'].
- unfold is_odd in Hodd. simpl in Hodd. discriminate.
- simpl factor2_bounded.
unfold is_odd in Hodd.
simpl in Hodd.
rewrite Hodd.
reflexivity.
Qed.

(* Lemma: factor2 of an odd number multiplied by a power of 2 *)
Lemma factor2_of_odd_mul_pow2 :
  forall d n,
    is_odd n ->
    factor2 (n * 2 ^ d) = (d, n).
Proof.
intros d n Hodd_n.
destruct d as [|d'].
- simpl.
rewrite Nat.mul_1_r.
exact (factor2_of_odd n Hodd_n).
- remember (factor2 (n * 2 ^ S d')) as p eqn:Hp.
destruct p as [d0 q].
pose proof (factor2_spec_decomp (n * 2 ^ S d')) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite <- Hp in Hdecomp.
assert (Hn_ge1 : n >= 1) by (apply is_odd_ge1; exact Hodd_n).
assert (Hprod_ge1 : n * 2 ^ S d' >= 1).
{
assert (Hn1 : 1 <= n) by lia.
assert (Hpow1 : 1 <= 2 ^ S d') by apply pow2_ge1.
replace 1 with (1 * 1) by lia.
apply Nat.mul_le_mono; assumption.
}
assert (Hodd_q : is_odd q).
{
pose proof (factor2_spec_odd (n * 2 ^ S d') Hprod_ge1) as H.
unfold factor2_odd in H.
rewrite <- Hp in H.
cbn [fst snd] in H.
exact H.
}
assert (Hpoweq : 2 ^ S d' * n = 2 ^ d0 * q).
{
pose proof Hdecomp as H.
cbn [fst snd] in H.
rewrite (Nat.mul_comm n (2 ^ S d')) in H.
rewrite (Nat.mul_comm q (2 ^ d0)) in H.
exact H.
}
assert (Hd0_ge1 : d0 >= 1).
{
destruct d0 as [|d0'].
- assert (Heven_pow : Nat.even (2 ^ S d') = true) by (apply power_2_even_property; lia).
assert (Heven_lhs : Nat.even (2 ^ S d' * n) = true).
{ rewrite Nat.even_mul. rewrite Heven_pow. simpl. reflexivity. }
assert (Heven_rhs : Nat.even (2 ^ 0 * q) = true).
{ rewrite <- Hpoweq. exact Heven_lhs. }
replace (2 ^ 0 * q) with q in Heven_rhs by (simpl; lia).
unfold is_odd in Hodd_q.
rewrite Hodd_q in Heven_rhs.
discriminate.
- lia.
}
pose proof
(pow2_times_odd_unique (S d') d0 n q
ltac:(lia) Hd0_ge1
ltac:(unfold is_odd in Hodd_n; exact Hodd_n)
ltac:(unfold is_odd in Hodd_q; exact Hodd_q)
Hpoweq) as [Hd_eq Hq_eq].
subst d0 q.
reflexivity.
Qed.

Lemma odd_2n_plus_1 : forall n, is_odd (2 * n + 1).
Proof.
intro n.
unfold is_odd.
rewrite Nat.even_add.
rewrite Nat.even_mul.
simpl.
reflexivity.
Qed.

(* Theorem: equivalence between macrostep and R1R0 sequence computation *)
Theorem macrostep_R1R0_equivalence :
  forall d0 n0 d1 n1 m0 m1 m2,
    is_odd n0 ->
    d1 >= 1 ->
    m0 = n0 * 2^d0 ->
    m1 = n0 ->
    m1 = valid_R1R0_entry_number d1 n1 ->
    m2 = 2 * 3^d1 * n1 + (3^d1 - 1) ->
    m2 = sequence_end m1 (repeat_R1R0 d1) /\
    canonical_mod62_macrostep_end m0 = m2.
Proof.
intros d0 n0 d1 n1 m0 m1 m2 Hodd Hd1_ge1 Hm0 Hm1 Hm1_R1R0 Hm2.
split.
- subst m2.
rewrite Hm1_R1R0.
symmetry.
apply repeat_R1R0_output_closed_form_no_div; lia.
- subst m0 m1 m2.
unfold canonical_mod62_macrostep_end.
assert (Hfac0 : factor2 (n0 * 2 ^ d0) = (d0, n0)).
{ apply factor2_of_odd_mul_pow2; exact Hodd. }
pose proof (valid_R1R0_entry_number_plus1 d1 n1) as Hplus.
assert (Hn0p1 : n0 + 1 = 2 ^ d1 * (2 * n1 + 1)).
{ rewrite Hm1_R1R0. exact Hplus. }
assert (Hfac1 : factor2 (n0 + 1) = (d1, 2 * n1 + 1)).
{
rewrite Hn0p1.
rewrite Nat.mul_comm.
apply factor2_of_odd_mul_pow2.
apply odd_2n_plus_1.
}
rewrite Hfac0.
simpl.
rewrite Hfac1.
simpl.
rewrite Hm1_R1R0.
apply repeat_R1R0_output_closed_form_no_div; lia.
Qed.

Theorem R1R0_sequence_fixed_point_unique :
  forall d n,
    d >= 1 -> n >= 0 ->
    sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d)
      = valid_R1R0_entry_number d n ->
    valid_R1R0_entry_number d n = 2.
Proof.
intros d n Hd Hn Hfix.
pose proof (repeat_R1R0_output_closed_form_no_div d n Hd Hn) as Hclosed.
rewrite Hclosed in Hfix.
unfold valid_R1R0_entry_number in Hfix.
assert (Hpow3_ge1 : 1 <= 3 ^ d) by apply pow3_ge1.
assert (Hpow2_ge1 : 1 <= 2 ^ d) by apply pow2_ge1.
assert (Hadd :
2 * 3 ^ d * n + (3 ^ d - 1) + 1 =
2 * (2 ^ d) * n + (2 ^ d - 1) + 1).
{ rewrite Hfix. reflexivity. }
rewrite <- Nat.add_assoc in Hadd.
rewrite <- Nat.add_assoc in Hadd.
replace ((3 ^ d - 1) + 1) with (3 ^ d) in Hadd by
(symmetry; apply Nat.sub_add; exact Hpow3_ge1).
replace ((2 ^ d - 1) + 1) with (2 ^ d) in Hadd by
(symmetry; apply Nat.sub_add; exact Hpow2_ge1).
assert (Hprod : 3 ^ d * (2 * n + 1) = 2 ^ d * (2 * n + 1)).
{
replace (2 * 3 ^ d * n + 3 ^ d) with (3 ^ d * (2 * n + 1)) in Hadd by ring.
replace (2 * 2 ^ d * n + 2 ^ d) with (2 ^ d * (2 * n + 1)) in Hadd by ring.
exact Hadd.
}
assert (Hnz : 2 * n + 1 <> 0) by lia.
pose proof (Nat.mul_cancel_r (3 ^ d) (2 ^ d) (2 * n + 1) Hnz) as Hcancel.
assert (Heqpow : 3 ^ d = 2 ^ d) by (apply (proj1 Hcancel); exact Hprod).
assert (Hfalse : False).
{
pose proof (pow3_gt_pow2 d Hd) as Hgt.
lia.
}
exact (False_rect _ Hfalse).
Qed.

(* Theorem: contribution equivalence for macrostep R1R0 chains *)
Theorem macrostep_R1R0_contribution_equivalence :
  forall m0 d0 n0 d1 n1,
    factor2 m0 = (d0, n0) ->
    factor2 (n0 + 1) = (d1, 2 * n1 + 1) ->
    sum_contributions (extract_simple_chains (canonical_mod62_macrostep_chains m0)) = d0 + 1.
Proof.
intros m0 d0 n0 d1 n1 Hfac0 _Hfac1.
exact (canonical_mod62_macrostep_contribution m0 d0 n0 Hfac0).
Qed.

Fixpoint R1R0_sequence_iterated (t : nat) (m0 : nat) : nat :=
  match t with
  | 0 => m0
  | S t' =>
      let '(d0, n0) := factor2 m0 in
      let m1 := n0 in
      let '(d1, _) := factor2 (m1 + 1) in
      R1R0_sequence_iterated t' (sequence_end m1 (repeat_R1R0 d1))
  end.

Lemma canonical_mod62_iterated_end_eq_R1R0_sequence_iterated :
  forall t m0,
    canonical_mod62_iterated_end t m0 = R1R0_sequence_iterated t m0.
Proof.
induction t as [|t IH]; intro m0.
- reflexivity.
- simpl.
unfold canonical_mod62_macrostep_end.
destruct (factor2 m0) as [d0 n0] eqn:Hp0.
simpl.
destruct (factor2 (n0 + 1)) as [d1 q1] eqn:Hp1.
simpl.
exact (IH _).
Qed.

(* Theorem: mod6=2 orbit macrostep is equivalent to R1R0 sequence *)
Theorem mod62_orbit_macrostep_R1R0_equivalence :
  forall m0,
    m0 mod 6 = 2 ->
    forall t,
      canonical_mod62_iterated_end t m0 = R1R0_sequence_iterated t m0.
Proof.
intros m0 _Hm0_mod6 t.
exact (canonical_mod62_iterated_end_eq_R1R0_sequence_iterated t m0).
Qed.

Lemma count_operations_canonical_chain_any :
  forall b d,
    count_operations (canonical_chain b d) =
      (if b then (d + 1, d) else (d + 1, 1)).
Proof.
intros [] d; unfold canonical_chain; simpl.
- rewrite (surjective_pairing (count_operations (repeat_R1R0 d ++ [R0]))).
rewrite count_R0_repeat_R1R0_plus_R0 by lia.
rewrite count_R1_repeat_R1R0_plus_R0 by lia.
reflexivity.
- rewrite (surjective_pairing (count_operations (repeat_R0 d ++ [R1; R0]))).
rewrite count_R0_repeat_R0_plus_R1R0 by lia.
rewrite count_R1_repeat_R0_plus_R1R0 by lia.
reflexivity.
Qed.

(* Theorem: R0 advantage is preserved in macrostep R1R0 chains *)
Theorem macrostep_R1R0_R0_advantage_preserve :
  forall m0 d0 n0 d1 n1,
    factor2 m0 = (d0, n0) ->
    factor2 (n0 + 1) = (d1, 2 * n1 + 1) ->
    let chains := canonical_mod62_macrostep_chains m0 in
    let total_seq := concat (map (fun '(b, d, _, _, _) => canonical_chain b d) chains) in
    fst (count_operations total_seq) - snd (count_operations total_seq) = d0 + 1.
Proof.
intros m0 d0 n0 d1 n1 Hfac0 Hfac1.
unfold canonical_mod62_macrostep_chains.
rewrite Hfac0.
rewrite Hfac1.
cbn [map concat].
rewrite app_nil_r.
rewrite count_operations_app.
rewrite count_operations_canonical_chain_any.
rewrite count_operations_canonical_chain_any.
simpl.
lia.
Qed.