Load "collatz_part_15.v".
Require Import Arith.
Require Import Nat.
Require Import Lia.


(* ============================================================= *)
(* 收敛分析(核心闭式 + 基本界) *)
Theorem collatz_macro_core : forall m,
  m >= 1 -> is_odd m ->
  exists d n,
    d >= 1 /\ n >= 0 /\
    m = valid_R1R0_entry_number d n /\
    let k := 3^d * n + (3^d - 1) / 2 in
    sequence_end m (repeat_R1R0 d) = 2 * k /\
    3^d * n <= k /\ k < 3^d * (n + 1).
Proof.
  (* 证明计划：
     1. 用 odd_eq_R1R0_entry_number 得到 d,n.
     2. 用 repeat_R1R0_output_closed_form_no_div 得到闭式。
     3. 定义 k 并重写；界来自 R1R0_bounds_summary (将 2*k 代入)。 *)
Admitted.

(* ============================================================= *)
(* 提取下一奇数（去除二因子）所需的幂次：宏步输出 2*k = 3^d*(2n+1) -1 *)
(* 通过对 2*k 进行 2 进制分解，得到 2^s * o (o 奇) 与 s>=1 *)

Theorem collatz_next_odd : forall m,
  m >= 1 -> is_odd m ->
  exists d n s o,
    d >= 1 /\ n >= 0 /\
    m = valid_R1R0_entry_number d n /\
    s >= 1 /\ o >= 1 /\ is_odd o /\
    (* 完全 2 因子分解 *)
    sequence_end m (repeat_R1R0 d) = 2^s * o /\
    (* 界用于后续增长/下降比较 *)
    3^d * n <= (3^d * n + (3^d - 1) / 2) < 3^d * (n + 1).
Proof.
  (* 证明计划：
     1. 复用 collatz_macro_core 得到 d,n 与 2*k 闭式。
     2. 设 K := 3^d * n + (3^d -1)/2, out = 2*K.
     3. out 是偶且 >=2 -> 用 power2_odd_decomposition (或自建引理) 得到 out = 2^s * o, o 奇。
     4. 代回。界直接由 core 定理即可。 *)
Admitted.

(* 说明：
   - collatz_macro_core 是之前复杂定理的“去分类”骨架，避免引入 k 再度分类的噪声。
   - collatz_next_odd 为实际收敛讨论提供：从奇数 m 到下一个“精简奇数” o 的宏步过渡。
   - 若需要进一步比较 o 与 m，可结合第15部分的对数上界引理对 d 进行界定，再将 o 表达成 m 的函数。 *)
