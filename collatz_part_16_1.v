Load "collatz_part_16.v".

(* Collatz Pattern Cycle Deterministic: Proves that for any starting value m ≥ 1 the Collatz sequence follows a deterministic cycle pattern between R1R0 and R0R0 entries *)
Theorem collatz_pattern_cycle_deterministic : forall m,
  m >= 1 ->
  (exists d n Send d' n',
      d >= 1 /\ n >= 0 /\ m = valid_R1R0_entry_number d n /\
      sequence_end m (repeat_R1R0 d) = Send /\
      is_even Send /\
      build_k_steps m d = repeat_R1R0 d /\
      build_k_steps m (S d) = repeat_R1R0 d ++ [R0] /\
      d' >= 1 /\ n' >= 1 /\ is_odd n' /\
      Send = valid_R0R0_entry_number d' n' /\
      sequence_end Send (repeat_R0 d') = n' /\
      build_k_steps Send d' = repeat_R0 d' /\
      build_k_steps Send (S d') = repeat_R0 d' ++ [R1; R0] /\
      (forall d0 n0, d0 >= 1 -> n0 >= 0 -> m = valid_R1R0_entry_number d0 n0 -> d0 = d /\ n0 = n) /\
      (forall d0 n0, d0 >= 1 -> n0 >= 1 -> is_odd n0 -> Send = valid_R0R0_entry_number d0 n0 -> d0 = d' /\ n0 = n')) \/
  (exists d n Send d' n' NextEven,
    d >= 1 /\ n >= 1 /\ is_odd n /\ m = valid_R0R0_entry_number d n /\
    sequence_end m (repeat_R0 d) = Send /\
    is_odd Send /\
    build_k_steps m d = repeat_R0 d /\
    build_k_steps m (S d) = repeat_R0 d ++ [R1; R0] /\
    d' >= 1 /\ n' >= 0 /\ Send = valid_R1R0_entry_number d' n' /\
    sequence_end Send (repeat_R1R0 d') = NextEven /\ is_even NextEven /\
    build_k_steps Send d' = repeat_R1R0 d' /\
    build_k_steps Send (S d') = repeat_R1R0 d' ++ [R0] /\
    (forall d0 n0, d0 >= 1 -> n0 >= 1 -> is_odd n0 -> m = valid_R0R0_entry_number d0 n0 -> d0 = d /\ n0 = n) /\
    (forall d0 n0, d0 >= 1 -> n0 >= 0 -> Send = valid_R1R0_entry_number d0 n0 -> d0 = d' /\ n0 = n')).
Proof.
intros m Hm.
pose proof (build_k_steps_numeric_canonical m Hm) as Hcanonical.
destruct Hcanonical as
[ [d [n [Hd [Hn [Hmdef [Hbuild [Hrange Hunique]]]]]]] |
[d [n [Hd [Hn [Hodd [Hmdef [Hbuild [Hseq_end Hunique]]]]]]]] ].
-
pose proof (odd_leads_R1R0_then_R0_pattern m d n Hm Hd Hn Hmdef) as Hodd_cycle.
destruct Hodd_cycle as [Send [Hseq_m [Heven_send [Hbounds [Hnext_step Huniq_m]]]]].
destruct Hbounds as [Hlow [Hhigh Hmin]].
assert (Hpow_pos : 3 ^ d - 1 >= 2).
{ replace 2 with (3^1 - 1) by (simpl; reflexivity).
apply Nat.sub_le_mono_r.
apply Nat.pow_le_mono_r; lia. }
assert (Hone_le_powminus : 1 <= 3 ^ d - 1) by lia.
assert (HSend_ge1 : Send >= 1) by (eapply Nat.le_trans; [exact Hone_le_powminus | exact Hmin]).
pose proof (build_k_steps_numeric_canonical Send HSend_ge1) as Hsend_canon.
destruct Hsend_canon as
[ [dc [nc [Hdc [Hnc [HSendDef [Hsend_build [Hsend_bounds Hsend_unique]]]]]]] |
[dc [nc [Hdc [Hnc [Hodd_nc [HSendDef [Hsend_build [Hsend_end Hsend_unique]]]]]]]] ].
+
exfalso.
pose proof (valid_R1R0_entry_number_is_odd dc nc Hdc Hnc) as Hodd_send_again.
unfold is_odd in Hodd_send_again.
rewrite <- HSendDef in Hodd_send_again.
unfold is_even in Heven_send.
rewrite Hodd_send_again in Heven_send; discriminate.
+
pose proof (even_leads_R0_then_R1R0_pattern Send dc nc HSend_ge1 Hdc Hnc Hodd_nc HSendDef) as Heven_cycle.
destruct Heven_cycle as [Send2 [Hseq_send [Hodd_Send2 [Hsend2_eq [Hnext_ops Huniq_send]]]]].
assert (Hseq_send_nc : sequence_end Send (repeat_R0 dc) = nc) by (rewrite <- Hsend2_eq; exact Hseq_send).
left.
exists d; exists n; exists Send; exists dc; exists nc.
split; [exact Hd |].
split; [exact Hn |].
split; [exact Hmdef |].
split; [exact Hseq_m |].
split; [exact Heven_send |].
split; [exact Hbuild |].
split; [exact Hnext_step |].
split; [exact Hdc |].
split; [exact Hnc |].
split; [exact Hodd_nc |].
split; [exact HSendDef |].
split; [exact Hseq_send_nc |].
split; [exact Hsend_build |].
split; [exact Hnext_ops |].
split; [exact Huniq_m |].
intros d0 n0 Hd0 Hn0 Hodd_n0 Hrepr0.
specialize (Huniq_send d0 n0 Hd0 Hn0 Hodd_n0 Hrepr0) as [Hd_eq Hn_eq]; split; assumption.
-
pose proof (even_leads_R0_then_R1R0_pattern m d n Hm Hd Hn Hodd Hmdef) as Heven_cycle.
destruct Heven_cycle as [Send [Hseq_m [Hodd_send [Hsend_eq [Hnext_step Huniq_m]]]]].
assert (HSend_ge1 : Send >= 1) by lia.
pose proof (build_k_steps_numeric_canonical Send HSend_ge1) as Hsend_canon.
destruct Hsend_canon as
[ [dc [nc [Hdc [Hnc [HSendDef [Hsend_build [Hsend_bounds Hsend_unique]]]]]]] |
[dc [nc [Hdc [Hnc [Hodd_nc [HSendDef [Hsend_build [Hsend_end Hsend_unique]]]]]]]] ].
+
pose proof (odd_leads_R1R0_then_R0_pattern Send dc nc HSend_ge1 Hdc Hnc HSendDef) as Hodd_cycle.
destruct Hodd_cycle as [Next [Hseq_send [Heven_next [Hnext_bounds [Hnext_ops Huniq_send]]]]].
right.
exists d; exists n; exists Send; exists dc; exists nc; exists Next.
split; [exact Hd |].
split; [exact Hn |].
split; [exact Hodd |].
split; [exact Hmdef |].
split; [exact Hseq_m |].
split; [exact Hodd_send |].
split; [exact Hbuild |].
split; [exact Hnext_step |].
split; [exact Hdc |].
split; [exact Hnc |].
split; [exact HSendDef |].
split; [exact Hseq_send |].
split; [exact Heven_next |].
split; [exact Hsend_build |].
split; [exact Hnext_ops |].
split; [exact Huniq_m |].
intros d0 n0 Hd0 Hn0 Hrepr0.
specialize (Huniq_send d0 n0 Hd0 Hn0 Hrepr0) as [Hd_eq Hn_eq]; split; assumption.
+
exfalso.
pose proof (valid_R0R0_entry_number_properties dc nc Hdc Hnc) as [_ Heven_send].
unfold is_even in Heven_send.
rewrite <- HSendDef in Heven_send.
unfold is_odd in Hodd_send.
rewrite Heven_send in Hodd_send; discriminate.
Qed.


(* Collatz cycle branch theorem *)
Theorem collatz_cycle : forall m d n,
  (R1R0_entry m d n) \/ (R0R0_entry m d n) ->
  (exists Send d' n',
      sequence_end m (repeat_R1R0 d) = Send /\
      is_even Send /\
      R0R0_entry Send d' n' /\
      build_k_steps m (S d) = repeat_R1R0 d ++ [R0]) \/
  (exists Send d' n',
      sequence_end m (repeat_R0 d) = Send /\
      is_odd Send /\
      R1R0_entry Send d' n' /\
      build_k_steps m (S d) = repeat_R0 d ++ [R1; R0]).
Proof.
intros m d n Hentry.
destruct Hentry as [H1 | H0].
- destruct (next_entry_from_R1R0 m d n H1) as (Send & d' & n' & Hseq & Heven & Hr0 & Hbuild).
left.
exists Send, d', n'.
split.
+ exact Hseq.
+ split.
* exact Heven.
* split.
-- exact Hr0.
-- exact Hbuild.
- destruct (next_entry_from_R0R0 m d n H0) as (Send & d' & n' & Hseq & Hodd & Hr1 & Hbuild).
right.
exists Send, d', n'.
split.
+ exact Hseq.
+ split.
* exact Hodd.
* split.
-- exact Hr1.
-- exact Hbuild.
Qed.