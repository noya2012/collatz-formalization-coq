Load "collatz_part_15.v".
Require Import Arith.
Require Import Nat.
Require Import Lia.

(* ============================================================= *)
(* 第16部分重新规划：                                               *)
(* 原始两个定理 collatz_behavior_chain_odd / collatz_behavior_chain  *)
(* 声称：对奇数 m，经若干 R1R0 模式后得到的 k 不是 1 就是奇数。        *)
(* 反例：m = 3 (d=2,n=0) => repeat_R1R0 2 输出 8 = 2 * 4, k = 4 为偶数且 >1 *)
(* 因此原定理为假。现基于第14部分 canonical / numeric 定理改写。      *)
(* 参考：build_k_steps_numeric_canonical, complete_number_canonical_classification *)
(* ============================================================= *)

(* 反例文档化：证明留空占位 *)
Lemma collatz_behavior_chain_old_counterexample :
  let m := 3 in m = valid_R1R0_entry_number 2 0 /\
  is_odd m /\
  exists k, sequence_end m (repeat_R1R0 2) = 2 * k /\ k = 4 /\ Nat.even k = true.
Proof.
  (* 细化可使用 repeat_R1R0_output_closed_form_no_div 展开：
     sequence_end (valid_R1R0_entry_number 2 0) (repeat_R1R0 2)
     = 2 * 3^2 * 0 + (3^2 - 1) = 8. *)
  (* Admitted 暂存 *)
Admitted.

(* ============================================================= *)
(* 精炼宏步奇数输入行为链：输出闭式 + k 的规范分支分类 + 数值界 *)
Theorem collatz_behavior_chain_odd_refined : forall m,
  m >= 1 -> is_odd m ->
  exists d n k,
    d >= 1 /\ n >= 0 /\
    m = valid_R1R0_entry_number d n /\
    (* 输出为 2*k 且 k 给出闭式 *)
    sequence_end m (repeat_R1R0 d) = 2 * k /\
    k = 3^d * n + (3^d - 1) / 2 /\
    (* 单步 R0 解出 k *)
    sequence_end (2 * k) [R0] = k /\
    (* k 的规范分支分类（可能偶也可能奇，避免旧错误分类） *)
    (
      (exists d' n', d' >= 1 /\ n' >= 0 /\ k = valid_R1R0_entry_number d' n' /\ build_k_steps k d' = repeat_R1R0 d') \/
      (exists d' n', d' >= 1 /\ n' >= 1 /\ is_odd n' /\ k = valid_R0R0_entry_number d' n' /\ build_k_steps k d' = repeat_R0 d')
    ) /\
    (* 数值界从 build_k_steps_numeric_canonical 对应部分提炼到 k *)
    3^d * n <= k /\ k < 3^d * (n + 1) /\ (3^d - 1) / 2 <= k.
Proof.
  (* 证明思路草稿：
     1. 用 odd_eq_R1R0_entry_number 得到 d,n.
     2. 用 repeat_R1R0_output_closed_form_no_div 得出输出 = 2*3^d*n + (3^d -1) = 2*k.
        定义 k := 3^d*n + (3^d -1)/2.
     3. 验证 k >= 1：来自 3^d -1 >=0 与界。
     4. sequence_end (2*k) [R0] = k 使用 even_div2_mul2.
     5. 对 k 用 complete_number_canonical_classification 分类。
     6. 数值界：从 R1R0_bounds_summary 将 out = 2*k 边界除以 2。
     占位暂存。 *)
Admitted.

(* 统一命名版本（与上面等价，仅为兼容以前使用者） *)
Theorem collatz_behavior_chain_refined : forall m,
  m >= 1 -> is_odd m ->
  exists d n k,
    d >= 1 /\ n >= 0 /\
    m = valid_R1R0_entry_number d n /\
    sequence_end m (repeat_R1R0 d) = 2 * k /\
    k = 3^d * n + (3^d - 1) / 2 /\
    sequence_end (2 * k) [R0] = k /\
    (
      (exists d' n', d' >= 1 /\ n' >= 0 /\ k = valid_R1R0_entry_number d' n' /\ build_k_steps k d' = repeat_R1R0 d') \/
      (exists d' n', d' >= 1 /\ n' >= 1 /\ is_odd n' /\ k = valid_R0R0_entry_number d' n' /\ build_k_steps k d' = repeat_R0 d')
    ) /\
    3^d * n <= k /\ k < 3^d * (n + 1) /\ (3^d - 1) / 2 <= k.
Proof.
Admitted.

(* 抽取下一步：给出 k 及继续/终止标志（k=1 或继续分类） *)
Corollary collatz_behavior_chain_next_step : forall m,
  m >= 1 -> is_odd m ->
  exists k,
    k >= 1 /\
    (exists d n, d >= 1 /\ n >= 0 /\ m = valid_R1R0_entry_number d n /\ sequence_end m (repeat_R1R0 d) = 2 * k /\ k = 3^d * n + (3^d - 1)/2) /\
    (k = 1 \/
      (exists d' n', d' >= 1 /\ n' >= 0 /\ k = valid_R1R0_entry_number d' n') \/
      (exists d'' n'', d'' >= 1 /\ n'' >= 1 /\ is_odd n'' /\ k = valid_R0R0_entry_number d'' n'')).
Proof.
Admitted.

(* 最简“终止或继续”标志：k=1 或 k>=2 *)
Corollary collatz_behavior_chain_termination_flag : forall m,
  m >= 1 -> is_odd m ->
  exists k, k >= 1 /\
    (exists d n, d >= 1 /\ n >= 0 /\ m = valid_R1R0_entry_number d n /\ sequence_end m (repeat_R1R0 d) = 2 * k) /\
    (k = 1 \/ k >= 2).
Proof.
Admitted.
