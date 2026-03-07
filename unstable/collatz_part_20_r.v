Load "collatz_part_20.v".

Local Open Scope nat.


(* Maximum element of a list *)
Fixpoint list_max (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (list_max xs)
  end.

(* List max is an upper bound *)
Lemma list_max_ge :
  forall x l,
    In x l ->
    x <= list_max l.
Proof.
intros x l Hin.
induction l as [|a l IH]; simpl in *.
- contradiction.
- destruct Hin as [<- | Hin].
+ apply Nat.le_max_l.
+ eapply Nat.le_trans; [exact (IH Hin)|].
apply Nat.le_max_r.
Qed.

(* List max is in the list *)
Lemma list_max_in :
  forall l,
    l <> nil ->
    In (list_max l) l.
Proof.
intros l Hne.
induction l as [|a l IH]; [contradiction|].
destruct l as [|b l'].
- simpl.
left.
rewrite Nat.max_l by lia.
reflexivity.
- simpl.
set (m := list_max (b :: l')).
destruct (le_dec a m) as [Hle | Hgt].
+
right.
assert (Hin_m : In m (b :: l')).
{ apply IH. discriminate. }
rewrite Nat.max_r by exact Hle.
exact Hin_m.
+
left.
assert (Hm_lt : m < a) by lia.
rewrite Nat.max_l by (apply Nat.lt_le_incl; exact Hm_lt).
reflexivity.
Qed.

(* Orbit of a cycle *)
Definition canonical_mod62_orbit (t : nat) (m0 : nat) : list nat :=
  map (fun i => canonical_mod62_iterated_end i m0) (seq 0 t).

(* Orbit is nonempty when t>=1 *)
Lemma canonical_mod62_orbit_nonempty :
  forall t m0,
    t >= 1 ->
    canonical_mod62_orbit t m0 <> nil.
Proof.
intros t m0 Ht.
unfold canonical_mod62_orbit.
destruct t; [lia|].
simpl. discriminate.
Qed.

(* Iterated end commutes with macrostep *)
Lemma canonical_mod62_iterated_end_comm :
  forall i m0,
    canonical_mod62_iterated_end i (canonical_mod62_macrostep_end m0) =
      canonical_mod62_macrostep_end (canonical_mod62_iterated_end i m0).
Proof.
induction i as [|i IH]; intro m0.
- simpl. reflexivity.
- simpl.
rewrite IH.
reflexivity.
Qed.

(* Iterated end at successor *)
Lemma canonical_mod62_iterated_end_succ :
  forall i m0,
    canonical_mod62_iterated_end (S i) m0 =
      canonical_mod62_macrostep_end (canonical_mod62_iterated_end i m0).
Proof.
intros i m0.
simpl.
apply canonical_mod62_iterated_end_comm.
Qed.

(* Iterated end is in orbit *)
Lemma In_canonical_mod62_orbit_iterated_end :
  forall t m0 i,
    i < t ->
    In (canonical_mod62_iterated_end i m0) (canonical_mod62_orbit t m0).
Proof.
intros t m0 i Hi.
unfold canonical_mod62_orbit.
apply (in_map (fun j => canonical_mod62_iterated_end j m0)).
apply in_seq.
lia.
Qed.

(* Cycle has a maximum element *)
Lemma canonical_mod62_cycle_has_max_element :
  forall t m0,
    canonical_mod62_cycle t m0 ->
    exists mmax,
      In mmax (canonical_mod62_orbit t m0) /\
      (forall x, In x (canonical_mod62_orbit t m0) -> x <= mmax).
Proof.
intros t m0 Hcyc.
unfold canonical_mod62_cycle in Hcyc.
destruct Hcyc as [Ht_ge1 [_ _]].
set (orb := canonical_mod62_orbit t m0).
exists (list_max orb).
split.
- apply list_max_in.
subst orb.
apply canonical_mod62_orbit_nonempty; exact Ht_ge1.
- intros x Hx.
subst orb.
apply list_max_ge; exact Hx.
Qed.

(* Cycle max step satisfies end <= max *)
Lemma canonical_mod62_cycle_has_max_step_le :
  forall t m0,
    canonical_mod62_cycle t m0 ->
    exists mmax,
      In mmax (canonical_mod62_orbit t m0) /\
      canonical_mod62_macrostep_end mmax <= mmax.
Proof.
intros t m0 Hcyc.
destruct (canonical_mod62_cycle_has_max_element t m0 Hcyc)
as [mmax [Hin Hle]].
exists mmax.
split; [exact Hin|].
(* The successor of any orbit element is again in the orbit (using the cycle
wrap-around at step t). *)
unfold canonical_mod62_cycle in Hcyc.
destruct Hcyc as [Ht_ge1 [Hm0_mod6 Hret]].
unfold canonical_mod62_orbit in Hin.
apply in_map_iff in Hin.
destruct Hin as [i [Hi_eq Hi_in]].
subst mmax.
apply in_seq in Hi_in.
destruct Hi_in as [Hi_ge0 Hi_lt_t].
assert (Hsucc_in :
In (canonical_mod62_iterated_end (S i) m0) (canonical_mod62_orbit t m0)).
{
destruct (Nat.lt_ge_cases (S i) t) as [Hlt | Hge].
- apply In_canonical_mod62_orbit_iterated_end; exact Hlt.
- assert (S i = t) by lia.
subst.
rewrite Hret.
unfold canonical_mod62_orbit.
change m0 with (canonical_mod62_iterated_end 0 m0).
apply (in_map (fun j => canonical_mod62_iterated_end j m0)).
apply in_seq.
lia.
}
specialize (Hle (canonical_mod62_iterated_end (S i) m0) Hsucc_in).
rewrite canonical_mod62_iterated_end_succ in Hle.
exact Hle.
Qed.

(* Max element implies successor <= max *)
Lemma max_element_implies_macrostep_end_le :
  forall t m0 mmax,
    canonical_mod62_cycle t m0 ->
    In mmax (canonical_mod62_orbit t m0) ->
    (forall x, In x (canonical_mod62_orbit t m0) -> x <= mmax) ->
    canonical_mod62_macrostep_end mmax <= mmax.
Proof.
intros t m0 mmax Hcyc Hin Hmax.
unfold canonical_mod62_cycle in Hcyc.
destruct Hcyc as [Ht_ge1 [_Hm0_mod6 Hret]].
unfold canonical_mod62_orbit in Hin.
apply in_map_iff in Hin.
destruct Hin as [i [Hi_eq Hi_in]].
subst mmax.
apply in_seq in Hi_in.
destruct Hi_in as [_Hi_ge0 Hi_lt_t].
assert (Hsucc_in :
In (canonical_mod62_iterated_end (S i) m0) (canonical_mod62_orbit t m0)).
{
destruct (Nat.lt_ge_cases (S i) t) as [Hlt | Hge].
- apply In_canonical_mod62_orbit_iterated_end; exact Hlt.
- assert (S i = t) by lia.
subst.
rewrite Hret.
unfold canonical_mod62_orbit.
change m0 with (canonical_mod62_iterated_end 0 m0).
apply (in_map (fun j => canonical_mod62_iterated_end j m0)).
apply in_seq.
lia.
}
specialize (Hmax (canonical_mod62_iterated_end (S i) m0) Hsucc_in).
rewrite canonical_mod62_iterated_end_succ in Hmax.
exact Hmax.
Qed.

(* Iterated end preserves mod6=2 *)
Lemma canonical_mod62_iterated_end_mod6 :
  forall t m0,
    m0 mod 6 = 2 ->
    canonical_mod62_iterated_end t m0 mod 6 = 2.
Proof.
induction t as [|t IH]; intros m0 Hm0.
- exact Hm0.
- simpl.
apply IH.
apply canonical_mod62_macrostep_end_mod6.
exact Hm0.
Qed.

(* Orbit elements have mod6=2 *)
Lemma In_canonical_mod62_orbit_mod6 :
  forall t m0 m,
    m0 mod 6 = 2 ->
    In m (canonical_mod62_orbit t m0) ->
    m mod 6 = 2.
Proof.
intros t m0 m Hm0 Hin.
unfold canonical_mod62_orbit in Hin.
apply in_map_iff in Hin.
destruct Hin as [i [Hi_eq Hi_in]].
rewrite <- Hi_eq.
apply canonical_mod62_iterated_end_mod6; exact Hm0.
Qed.

(* Max element forces not d0=1 and d1>=2 *)
Lemma nontrivial_cycle_max_element_forces_not_d0_eq1_d1_ge2 :
  forall t m0,
    canonical_mod62_nontrivial_cycle t m0 ->
    forall mmax d0 n0 d1 q1,
      In mmax (canonical_mod62_orbit t m0) ->
      (forall x, In x (canonical_mod62_orbit t m0) -> x <= mmax) ->
      factor2 mmax = (d0, n0) ->
      factor2 (n0 + 1) = (d1, q1) ->
      d0 <> 1 \/ d1 < 2.
Proof.
intros t m0 Hncyc mmax d0 n0 d1 q1 Hin Hmax Hfac0 Hfac1.
unfold canonical_mod62_nontrivial_cycle in Hncyc.
destruct Hncyc as [Hcyc _Hm0_ne2].
pose proof (max_element_implies_macrostep_end_le t m0 mmax Hcyc Hin Hmax) as Hle.
unfold canonical_mod62_cycle in Hcyc.
destruct Hcyc as [_Ht_ge1 [Hm0_mod6 _Hret]].
assert (Hmmax_mod6 : mmax mod 6 = 2).
{ apply (In_canonical_mod62_orbit_mod6 t m0 mmax Hm0_mod6 Hin). }
destruct (Nat.eq_dec d0 1) as [Hd0_eq1 | Hd0_ne1].
- subst d0.
right.
destruct (Nat.lt_ge_cases d1 2) as [Hd1_lt2 | Hd1_ge2]; [exact Hd1_lt2|].
exfalso.
pose proof
(canonical_mod62_macrostep_end_gt_self_if_d0_eq1_d1_ge2
mmax n0 d1 q1 Hmmax_mod6 Hfac0 Hfac1 Hd1_ge2) as Hgt.
lia.
- left. exact Hd0_ne1.
Qed.

(* Strict decrease when d0=1 and d1=1 *)
Lemma macrostep_end_lt_self_if_d0_eq1_d1_eq1 :
  forall m0 n0 q1,
    m0 mod 6 = 2 ->
    m0 <> 2 ->
    factor2 m0 = (1, n0) ->
    factor2 (n0 + 1) = (1, q1) ->
    canonical_mod62_macrostep_end m0 < m0.
Proof.
intros m0 n0 q1 Hm0_mod6 Hm0_ne2 Hfac0 Hfac1.
assert (Hm0_ge1 : m0 >= 1).
{
pose proof (Nat.div_mod m0 6 ltac:(lia)) as Hdiv.
rewrite Hm0_mod6 in Hdiv.
lia.
}
assert (Hn0_odd : is_odd n0).
{
pose proof (factor2_spec_odd m0 Hm0_ge1) as Hodd.
unfold factor2_odd in Hodd.
rewrite Hfac0 in Hodd.
cbn [snd] in Hodd.
exact Hodd.
}
pose proof (factor2_spec_decomp m0) as Hm0_decomp.
unfold factor2_odd, factor2_exp in Hm0_decomp.
rewrite Hfac0 in Hm0_decomp.
simpl in Hm0_decomp.
assert (Hn0_gt1 : n0 > 1).
{
destruct n0 as [|n0']; [discriminate Hn0_odd|].
destruct n0' as [|n0'']; [|lia].
rewrite Hm0_decomp in Hm0_ne2.
simpl in Hm0_ne2.
contradiction.
}
unfold canonical_mod62_macrostep_end.
rewrite Hfac0.
cbn.
rewrite Hfac1.
cbn.
unfold sequence_end.
cbn [repeat_R1R0 length nth_sequence_value].
unfold collatz_step.
rewrite Hn0_odd.
assert (Heven_3n0p1 : Nat.even (3 * n0 + 1) = true).
{
rewrite Nat.even_add.
rewrite Nat.even_mul.
rewrite Hn0_odd.
vm_compute.
reflexivity.
}
rewrite Heven_3n0p1.
rewrite Hm0_decomp.
cbn [Nat.pow].
apply (Nat.div_lt_upper_bound (3 * n0 + 1) 2 (n0 * 2) ltac:(lia)).
nia.
Qed.

(* Nontrivial cycle impossible if max forces growth *)
Theorem canonical_mod62_nontrivial_cycle_impossible_if_max_forces_d0_eq1_d1_ge2 :
  forall t m0,
    canonical_mod62_nontrivial_cycle t m0 ->
    (forall mmax d0 n0 d1 q1,
        In mmax (canonical_mod62_orbit t m0) ->
        canonical_mod62_macrostep_end mmax <= mmax ->
        factor2 mmax = (d0, n0) ->
        factor2 (n0 + 1) = (d1, q1) ->
        d0 = 1 /\ d1 >= 2) ->
    False.
Proof.
intros t m0 Hncyc Hforce.
unfold canonical_mod62_nontrivial_cycle in Hncyc.
destruct Hncyc as [Hcyc _Hm0_ne2].
destruct (canonical_mod62_cycle_has_max_step_le t m0 Hcyc)
as [mmax [Hin Hle]].
destruct (factor2 mmax) as [d0 n0] eqn:Hfac0.
destruct (factor2 (n0 + 1)) as [d1 q1] eqn:Hfac1.
destruct (Hforce mmax d0 n0 d1 q1 Hin Hle Hfac0 Hfac1) as [Hd0_eq1 Hd1_ge2].
subst d0.
unfold canonical_mod62_cycle in Hcyc.
destruct Hcyc as [_Ht_ge1 [Hm0_mod6 _Hret]].
assert (Hmmax_mod6 : mmax mod 6 = 2).
{ apply (In_canonical_mod62_orbit_mod6 t m0 mmax Hm0_mod6 Hin). }
pose proof
(canonical_mod62_macrostep_end_gt_self_if_d0_eq1_d1_ge2
mmax n0 d1 q1 Hmmax_mod6 Hfac0 Hfac1 Hd1_ge2) as Hgt.
lia.
Qed.

(* End <= self implies not d0=1 and d1>=2 *)
Lemma canonical_mod62_macrostep_end_le_implies_not_d0_eq1_d1_ge2 :
  forall m0 d0 n0 d1 q1,
    m0 mod 6 = 2 ->
    factor2 m0 = (d0, n0) ->
    factor2 (n0 + 1) = (d1, q1) ->
    canonical_mod62_macrostep_end m0 <= m0 ->
    d0 <> 1 \/ d1 < 2.
Proof.
intros m0 d0 n0 d1 q1 Hm0_mod6 Hfac0 Hfac1 Hle.
destruct (Nat.eq_dec d0 1) as [Hd0_eq1 | Hd0_ne1].
- right.
destruct (Nat.lt_ge_cases d1 2) as [Hd1_lt2 | Hd1_ge2]; [exact Hd1_lt2|].
exfalso.
subst d0.
pose proof
(canonical_mod62_macrostep_end_gt_self_if_d0_eq1_d1_ge2
m0 n0 d1 q1 Hm0_mod6 Hfac0 Hfac1 Hd1_ge2) as Hgt.
lia.
- left. exact Hd0_ne1.
Qed.

(* Nontrivial cycle max element forces not d0=1 and d1>=2 *)
Theorem canonical_mod62_nontrivial_cycle_max_element_force_not_d0_eq1_d1_ge2 :
  forall t m0,
    canonical_mod62_nontrivial_cycle t m0 ->
    exists mmax d0 n0 d1 q1,
      In mmax (canonical_mod62_orbit t m0) /\
      canonical_mod62_macrostep_end mmax <= mmax /\
      factor2 mmax = (d0, n0) /\
      factor2 (n0 + 1) = (d1, q1) /\
      (d0 <> 1 \/ d1 < 2).
Proof.
intros t m0 Hncyc.
unfold canonical_mod62_nontrivial_cycle in Hncyc.
destruct Hncyc as [Hcyc _Hm0_ne2].
destruct (canonical_mod62_cycle_has_max_step_le t m0 Hcyc)
as [mmax [Hin Hle]].
destruct (factor2 mmax) as [d0 n0] eqn:Hfac0.
destruct (factor2 (n0 + 1)) as [d1 q1] eqn:Hfac1.
exists mmax, d0, n0, d1, q1.
repeat split; try assumption.
unfold canonical_mod62_cycle in Hcyc.
destruct Hcyc as [_Ht_ge1 [Hm0_mod6 _Hret]].
assert (Hmmax_mod6 : mmax mod 6 = 2).
{ apply (In_canonical_mod62_orbit_mod6 t m0 mmax Hm0_mod6 Hin). }
exact
(canonical_mod62_macrostep_end_le_implies_not_d0_eq1_d1_ge2
mmax d0 n0 d1 q1 Hmmax_mod6 Hfac0 Hfac1 Hle).
Qed.