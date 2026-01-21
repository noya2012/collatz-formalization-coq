# R1R0_bounds_summary - R1R0 Combined Bounds Summary

## Basic Information

- **Theorem Type**: Theorem
- **Location**: collatz_part_11.v:96-107
- **Description**: R1R0 Combined Bounds Summary: max(2*3^D*n, 3^D - 1) ≤ output ≤ 3^D*(2n+1)

## Theorem Statement

```coq
Theorem R1R0_bounds_summary : forall D n,
	D >= 1 -> n >= 0 ->
	let out := sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) in
		(2 * 3^D * n <= out) /\
		(3^D - 1 <= out) /\
		out <= 3^D * (2*n + 1).
```

## Theorem Purpose

This theorem provides a comprehensive three-part bound on the output of R1R0 operation sequences. Its purposes include:

1. **Quantitative Control**: Establishes both lower and upper bounds on R1R0 sequence outputs
2. **Growth Understanding**: Characterizes how the output grows as a function of parameters D and n
3. **Analysis Foundation**: Provides the key inequalities used in subsequent analysis and proofs
4. **Behavior Characterization**: Reveals important properties of R1R0 sequences through their bounds

## Theorem Properties

### Mathematical Properties

1. **Tight Bounds**: The bounds are reasonably tight and provide good control over the output
2. **Asymmetric Structure**: Two lower bounds (linear and constant) and one upper bound
3. **Monotonicity**: All bounds respect the monotonic behavior of the actual output
4. **Gap Analysis**: The ratio between upper and lower bounds is bounded by a small constant

### Structural Properties

- **Lower Bound 1 (Linear)**: 2 * 3^D * n ≤ output - dominant term for large n
- **Lower Bound 2 (Constant)**: 3^D - 1 ≤ output - ensures minimum even when n=0
- **Upper Bound**: output ≤ 3^D * (2n + 1) - ensures maximum growth control
- **Combined**: max(2*3^D*n, 3^D-1) ≤ output ≤ 3^D*(2n+1)

### Growth Rate Analysis

1. **In D (exponential)**:
   - All bounds scale as 3^D
   - Growth rate: exponential with base 3

2. **In n (linear)**:
   - Lower bounds: O(n) or constant
   - Upper bound: O(n)
   - Overall: linear in n

3. **Relative Error**:
   - Upper/lower ratio: approximately (2n+1)/(2n) for large n, approaching 1
   - Gap: upper - lower = 3^D for the linear lower bound case

## Technical Support

### Direct Dependencies

1. **repeat_R1R0_output_lower_bound_linear**
   - Location: collatz_part_11.v:76-83
   - Statement: `2 * 3^D * n <= sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D)`
   - Usage: Provides the first (linear) lower bound

2. **repeat_R1R0_output_lower_bound_const**
   - Location: collatz_part_11.v:86-93
   - Statement: `3^D - 1 <= sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D)`
   - Usage: Provides the second (constant) lower bound

3. **repeat_R1R0_output_upper_bound**
   - Location: collatz_part_11.v:65-73
   - Statement: `sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <= 3^D * (2 * n + 1)`
   - Usage: Provides the upper bound

### Indirect Support

1. **repeat_R1R0_output_closed_form_no_div**
   - Provides the exact formula: output = 2 * 3^D * n + (3^D - 1)
   - All three bounds are derived from this exact expression

2. **valid_R1R0_entry_number**
   - Characterizes the starting numbers for R1R0 patterns

3. **repeat_R1R0**
   - Generates the operation sequences

## Sufficient and Necessary Support

### Sufficient Conditions
- If D≥1 and n≥0, then all three bounds hold simultaneously
- The bounds are guaranteed for all valid inputs to the R1R0 pattern

### Necessary Conditions (for the bounds to be meaningful)
- The input must be of the form valid_R1R0_entry_number D n
- The operation sequence must be exactly repeat_R1R0 D
- The bounds only apply to this specific pattern

### Tightness Analysis

1. **Linear Lower Bound**:
   - Tight when n is large relative to 1
   - Gap: actual - bound = (3^D - 1), which is independent of n

2. **Constant Lower Bound**:
   - Tight when n=0 (exact equality)
   - For n>0, this bound is weaker than the linear bound

3. **Upper Bound**:
   - Tight when n=0 (actual = upper)
   - Gap: upper - actual = 3^D, independent of n

### Combined Lower Bound

The theorem provides two separate lower bounds, but they can be combined:
```
max(2 * 3^D * n, 3^D - 1) ≤ output
```

- For n ≥ 1: 2 * 3^D * n ≥ 2 * 3^D > 3^D - 1, so linear bound dominates
- For n = 0: linear bound = 0, constant bound = 3^D - 1, so constant bound dominates

Thus: combined lower bound = max(2*3^D*n, 3^D-1)

## Technical Features

### Proof Strategy

1. **Separate Proofs**: Each bound is proved separately using specialized lemmas
2. **Composition**: The three bounds are then combined using conjunction
3. **Direct Application**: The proof is essentially a composition of existing lemmas
4. **No New Logic**: The theorem itself adds no new reasoning, only organization

### Code Structure

```coq
Proof.
	intros D n HD Hn out.
	split.
	- apply repeat_R1R0_output_lower_bound_linear; assumption.
	- split.
		+ apply repeat_R1R0_output_lower_bound_const; assumption.
		+ apply repeat_R1R0_output_upper_bound; assumption.
Qed.
```

- **intros**: Introduces variables D, n, hypotheses, and defines `out`
- **split**: Splits the triple conjunction into three separate goals
- **apply ...; assumption**: Applies the specialized lemma and verifies hypotheses

### Key Technical Points

1. **Lemma Composition**: The theorem is a perfect example of composing smaller results into a more comprehensive statement
2. **Hypothesis Management**: All three lemmas require the same hypotheses (HD: D≥1, Hn: n≥0), which are efficiently reused
3. **Structure Clarity**: The proof structure mirrors the statement structure perfectly
4. **Verification Simplicity**: The proof is essentially three direct applications of existing lemmas

## Applications and Significance

1. **Growth Analysis**: Provides quantitative understanding of how R1R0 sequences grow
2. **Sequence Comparison**: Enables comparison of different R1R0 sequences via their parameters
3. **Convergence Studies**: The bounds help in analyzing convergence properties
4. **Advantage Counting**: The lower bounds contribute to R0 advantage analysis
5. **Inequality Proofs**: These inequalities are used as building blocks in more complex proofs

### Specific Applications

1. **Advantage Analysis**:
   - The linear lower bound shows that output grows at least as fast as 2*3^D*n
   - This growth rate is important for understanding R0 vs R1 operation balance

2. **Convergence Bounds**:
   - The upper bound limits how much an R1R0 sequence can grow
   - This is crucial for proving that sequences don't diverge to infinity

3. **Parameter Analysis**:
   - The bounds reveal how sensitive the output is to changes in D and n
   - Helps in understanding which parameters control the behavior

## Example Explanations

### Example 1: D=1, n=0
- **Starting number**: valid_R1R0_entry_number 1 0 = 1
- **Actual output**: 2 (1 → 4 → 2)
- **Linear lower bound**: 2*3^1*0 = 0 ≤ 2 ✓
- **Constant lower bound**: 3^1 - 1 = 2 ≤ 2 ✓ (tight!)
- **Upper bound**: 2 ≤ 3^1*(2*0+1) = 3 ✓ (tight!)
- **Status**: Both lower bounds and upper bound are tight

### Example 2: D=1, n=1
- **Starting number**: valid_R1R0_entry_number 1 1 = 5
- **Actual output**: 8 (5 → 16 → 8)
- **Linear lower bound**: 2*3^1*1 = 6 ≤ 8 ✓
- **Constant lower bound**: 3^1 - 1 = 2 ≤ 8 ✓
- **Upper bound**: 8 ≤ 3^1*(2*1+1) = 9 ✓
- **Gaps**: 
  - Linear lower: gap = 8-6 = 2
  - Upper: gap = 9-8 = 1

### Example 3: D=2, n=3
- **Starting number**: valid_R1R0_entry_number 2 3 = (2*4*3) + 3 = 27
- **Actual output**: 2*3^2*3 + (3^2-1) = 2*9*3 + 8 = 54 + 8 = 62
- **Linear lower bound**: 2*9*3 = 54 ≤ 62 ✓
- **Constant lower bound**: 9-1 = 8 ≤ 62 ✓
- **Upper bound**: 62 ≤ 9*(2*3+1) = 9*7 = 63 ✓
- **Gaps**:
  - Linear lower: gap = 62-54 = 8
  - Upper: gap = 63-62 = 1

### Example 4: D=3, n=5
- **Starting number**: valid_R1R0_entry_number 3 5 = (2*8*5) + 7 = 87
- **Actual output**: 2*27*5 + (27-1) = 270 + 26 = 296
- **Linear lower bound**: 2*27*5 = 270 ≤ 296 ✓
- **Constant lower bound**: 27-1 = 26 ≤ 296 ✓
- **Upper bound**: 296 ≤ 27*(2*5+1) = 27*11 = 297 ✓
- **Gaps**:
  - Linear lower: gap = 296-270 = 26
  - Upper: gap = 297-296 = 1

### Observations from Examples

1. **Constant lower bound**: Only tight when n=0, otherwise loose
2. **Linear lower bound**: Always has gap of (3^D-1)
3. **Upper bound**: Always has gap of 3^D (very tight!)
4. **Dominant lower bound**: For n≥1, linear bound dominates constant bound

## Related Theorems

- **repeat_R1R0_output_lower_bound_linear**: First lower bound (direct lemma)
- **repeat_R1R0_output_lower_bound_const**: Second lower bound (direct lemma)
- **repeat_R1R0_output_upper_bound**: Upper bound (direct lemma)
- **repeat_R1R0_output_closed_form_no_div**: Exact formula (foundation for all bounds)
- **R0R0_bounds_summary**: Analogous bounds for R0R0 patterns
- **global_mod62_advantage_growth_canonical**: Uses bounds in global analysis

## Historical Context

This theorem represents a synthesis of three separate analytical results into a comprehensive bounds theorem. Historically:
1. First, the exact closed form was derived (repeat_R1R0_output_closed_form_no_div)
2. Then, individual bounds were proved separately (linear, constant, upper)
3. Finally, these bounds were combined into this summary theorem

This structure demonstrates the incremental nature of mathematical formalization:
- Start with exact formulas
- Derive useful inequalities
- Compose into comprehensive results

## Connection to Overall Formalization

This theorem sits at a crucial point in the formalization:

1. **Upstream**: Depends on exact closed form and individual bound lemmas
2. **Downstream**: Feeds into global analysis and advantage growth theorems
3. **Parallel**: Complements R0R0 bounds for complete picture of both patterns

The bounds are used in:
- Proving R0 advantage properties
- Analyzing global behavior on mod6=2 orbits
- Establishing convergence characteristics
- Comparing different Collatz operation patterns

## Mathematical Significance

The three-part bound structure reveals important mathematical properties:

1. **Asymptotic Behavior**: For large n, output ~ 2*3^D*n (linear lower bound is asymptotically tight)

2. **Minimum Value**: Even when n=0, output = 3^D - 1 (constant lower bound is exact)

3. **Maximum Growth**: output grows at most as 3^D*(2n+1), which is very close to actual

4. **Growth Rate**: The output is sandwiched between two linear functions with similar slopes:
   - Lower: slope = 2*3^D
   - Upper: slope = 2*3^D
   - Difference: only the intercept varies (0 vs 3^D)

This tight control over the output is essential for proving global properties of Collatz sequences.
