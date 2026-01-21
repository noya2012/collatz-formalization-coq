# repeat_R1R0_output_closed_form_no_div - R1R0 Final Value Closed Form

## Basic Information

- **Theorem Type**: Corollary
- **Location**: collatz_part_11.v:51-60
- **Description**: Corollary of R1R0 Final Value Closed Form

## Theorem Statement

```coq
Corollary repeat_R1R0_output_closed_form_no_div : forall D n,
  D >= 1 -> n >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) = 2 * 3^D * n + (3^D - 1).
```

## Theorem Purpose

This corollary provides a clean, division-free closed-form expression for the output of R1R0 operation sequences. Its purposes include:

1. **Simplified Expression**: Removes the division by 2 present in the general closed form, providing a cleaner representation
2. **Direct Computation**: Allows direct calculation of R1R0 sequence output without intermediate division steps
3. **Arithmetic Foundation**: Serves as the basis for all subsequent bounds and growth analysis theorems
4. **Pattern Understanding**: Reveals the exact relationship between input parameters (D,n) and output value

## Theorem Properties

### Mathematical Properties

1. **Exact Formula**: Provides an exact arithmetic expression, not just bounds
2. **Integer-Valued**: The expression 2*3^D*n + (3^D-1) always yields an integer for natural D,n
3. **Monotonicity**: The output is monotonic in both D and n parameters
4. **Growth Rate**: Shows exponential growth in D (factor of 3^D) and linear growth in n

### Structural Properties

- **Linear in n**: For fixed D, output = (2*3^D)*n + (3^D-1) is linear in n with slope 2*3^D
- **Exponential in D**: For fixed n, output scales roughly as 3^D
- **Positive Offset**: Always has a constant term (3^D-1), ensuring minimum output even when n=0

## Technical Support

### Direct Dependence

1. **repeat_R1R0_output_closed_form**
   - Location: collatz_part_11.v:23-27
   - Statement:
     ```coq
     sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D)
       = 2 * (3^D * n + (3^D - 1) / 2)
     ```
   - Relationship: This corollary simplifies this expression by removing the division

2. **pow3_minus1_twice_half**
   - Function: Provides an identity that relates (3^D-1)/2 to integer form
   - Used in the proof to simplify the expression

3. **Nat.mul_add_distr_l**
   - Standard library lemma: Distributive law for multiplication over addition
   - Used to expand 2*(3^D*n + (3^D-1)/2)

### Definition Support

1. **valid_R1R0_entry_number**
   ```coq
   Definition valid_R1R0_entry_number (d n: nat) : nat := (2 * (2^d) * n) + (2^d - 1)
   ```
   - Characterizes starting numbers for R1R0 patterns

2. **repeat_R1R0**
   - Generates D consecutive R1R0 operation pairs
   - Each R1R0 pair: multiply by 3, add 1, then divide by 2

3. **sequence_end**
   - Applies the operation sequence to the starting number
   - Returns the final result

## Sufficient and Necessary Support

### Sufficient Conditions
- If D≥1 and n≥0, then the output formula holds exactly

### Necessary Conditions (derived from the lemma)
- The formula only applies to inputs of the form valid_R1R0_entry_number D n
- The operation sequence must be exactly repeat_R1R0 D (D consecutive R1R0 pairs)
- The formula is both necessary and sufficient for these conditions

### Derivation from General Closed Form
The general closed form is:
```
output = 2 * (3^D * n + (3^D - 1) / 2)
```

This corollary simplifies it to:
```
output = 2 * 3^D * n + (3^D - 1)
```

The simplification uses the identity:
```
2 * (A + B/2) = 2*A + B
```

## Technical Features

### Proof Strategy

1. **Rewrite with General Formula**: Applies the more general closed form theorem
2. **Distributive Law**: Uses distributivity to expand the expression
3. **Power Identity**: Applies pow3_minus1_twice_half to handle the division
4. **Arithmetic Simplification**: Uses lia (linear integer arithmetic) for final verification

### Code Structure

```coq
Proof.
  intros D n HD Hn.
	rewrite (repeat_R1R0_output_closed_form D n HD Hn).
	rewrite Nat.mul_add_distr_l.
	rewrite pow3_minus1_twice_half.
	lia.
Qed.
```

- **intros**: Introduces variables D, n and hypotheses HD (D≥1), Hn (n≥0)
- **rewrite ...**: Replaces the expression using the general closed form
- **rewrite Nat.mul_add_distr_l**: Applies distributive law: 2*(A+B) = 2*A + 2*B
- **rewrite pow3_minus1_twice_half**: Simplifies 2*(3^D-1)/2 to (3^D-1)
- **lia**: Completes the proof using linear arithmetic

### Key Technical Points

1. **Formula Simplification**: The main contribution is removing the division, making the formula cleaner
2. **Leveraged Proofs**: The proof is essentially a sequence of rewrites, leveraging earlier work
3. **Arithmetic Automation**: The final verification is automated, showing the power of the approach
4. **Type Preservation**: All transformations preserve the type (natural numbers) correctly

## Applications and Significance

1. **Bounds Computation**: Directly used in R1R0_bounds_summary to compute upper and lower bounds
2. **Growth Analysis**: Provides the foundation for analyzing how R1R0 patterns grow
3. **Sequence Prediction**: Allows exact prediction of R1R0 sequence outputs without simulation
4. **Comparison Analysis**: Enables comparison between different sequences (by comparing their closed forms)
5. **Optimization Studies**: Supports analysis of which sequences minimize or maximize growth

## Example Explanations

### Example 1: D=1, n=0
- **Starting number**: valid_R1R0_entry_number 1 0 = (2*2*0) + (2-1) = 1
- **Operations**: [R1; R0] (one R1R0 pair)
- **Process**: 1 → 4 (R1: 3*1+1) → 2 (R0: 4/2)
- **Formula**: 2*3^1*0 + (3^1-1) = 0 + 2 = 2 ✓

### Example 2: D=1, n=1
- **Starting number**: valid_R1R0_entry_number 1 1 = (2*2*1) + (2-1) = 4+3 = 7
- **Operations**: [R1; R0]
- **Process**: 7 → 22 (R1: 3*7+1) → 11 (R0: 22/2)
- **Formula**: 2*3^1*1 + (3^1-1) = 6 + 2 = 8

**Note**: Wait, this doesn't match! Let me recalculate:
- Process: 7 → 3*7+1 = 22 → 22/2 = 11
- But formula gives: 2*3*1 + 2 = 8

There seems to be a discrepancy. Let me re-examine...

Actually, let me check the valid_R1R0_entry_number definition:
valid_R1R0_entry_number D n = (2 * 2^D * n) + (2^D - 1)

For D=1, n=1: (2 * 2^1 * 1) + (2^1 - 1) = (2*2*1) + (2-1) = 4+1 = 5 (not 7!)

Let me redo this example correctly:

### Example 2 (Corrected): D=1, n=1
- **Starting number**: valid_R1R0_entry_number 1 1 = 5
- **Operations**: [R1; R0]
- **Process**: 5 → 16 (R1: 3*5+1) → 8 (R0: 16/2)
- **Formula**: 2*3^1*1 + (3^1-1) = 6 + 2 = 8 ✓

### Example 3: D=2, n=0
- **Starting number**: valid_R1R0_entry_number 2 0 = (2*4*0) + (4-1) = 3
- **Operations**: [R1; R0; R1; R0] (two R1R0 pairs)
- **Process**: 3 → 10 → 5 → 16 → 8
- **Formula**: 2*3^2*0 + (3^2-1) = 0 + 8 = 8 ✓

### Example 4: D=2, n=1
- **Starting number**: valid_R1R0_entry_number 2 1 = (2*4*1) + (4-1) = 8+3 = 11
- **Operations**: [R1; R0; R1; R0]
- **Process**: 11 → 34 → 17 → 52 → 26
- **Formula**: 2*3^2*1 + (3^2-1) = 18 + 8 = 26 ✓

### Example 5: D=3, n=2
- **Starting number**: valid_R1R0_entry_number 3 2 = (2*8*2) + (8-1) = 32+7 = 39
- **Operations**: [R1; R0; R1; R0; R1; R0] (three R1R0 pairs)
- **Formula**: 2*3^3*2 + (3^3-1) = 2*27*2 + 26 = 108 + 26 = 134
- **Verification**: Apply operations to verify output is 134 ✓

## Related Theorems

- **repeat_R1R0_output_closed_form**: The more general lemma on which this corollary is based
- **R1R0_bounds_summary**: Uses this corollary to establish bounds
- **repeat_R1R0_output_upper_bound**: Upper bound derived from this closed form
- **repeat_R1R0_output_lower_bound_linear**: Lower bound derived from this closed form
- **repeat_R1R0_output_lower_bound_const**: Constant lower bound derived from this closed form

## Historical Context

This corollary represents a key simplification in the formalization. The general closed form theorem provides:
```
output = 2 * (3^D * n + (3^D - 1) / 2)
```

While mathematically correct, the division by 2 complicates analysis. This corollary removes that complication by providing:
```
output = 2 * 3^D * n + (3^D - 1)
```

This simplification:
- Makes the formula easier to use in proofs
- Eliminates concerns about divisibility
- Provides a more intuitive expression (sum of a linear term in n and a constant term)
- Facilitates automatic reasoning with linear arithmetic

## Connection to Bounds Analysis

The closed form formula is directly used to establish all the bounds in R1R0_bounds_summary:

1. **Lower Bound (Linear)**: 2 * 3^D * n ≤ output
   - Derived by dropping the constant term (3^D - 1)

2. **Lower Bound (Constant)**: 3^D - 1 ≤ output
   - Derived by dropping the linear term (2 * 3^D * n)

3. **Upper Bound**: output ≤ 3^D * (2n + 1)
   - Derivation: 2 * 3^D * n + (3^D - 1) ≤ 2 * 3^D * n + 3^D = 3^D * (2n + 1)

All three bounds follow naturally from this clean closed-form expression.
