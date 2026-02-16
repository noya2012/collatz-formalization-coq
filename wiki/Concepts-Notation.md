# Concepts & Notation - Quick Reference

## Operations

| Symbol | Name | Rule | Effect |
|--------|------|------|--------|
| **R0** | Divide by 2 | n → n/2 | Shrinks |
| **R1** | Collatz step | n → 3n+1 | Grows |

---

## Patterns

| Pattern | Composition | Entry Type |
|---------|-------------|------------|
| **R1R0** | R1 followed by R0 | Odd numbers |
| **R0R0** | Consecutive R0s | Even numbers |

---

## Entry Functions

### R1R0 Entry (Odd Numbers)

```
valid_R1R0_entry_number(d, n) = 2·2^d·n + (2^d - 1)
```

| Parameter | Meaning | Constraint |
|-----------|---------|------------|
| d | Depth (R1R0 pair count) | d ≥ 1 |
| n | Base parameter | n ≥ 0 |

**Output after R1R0^d**: `2·3^d·n + (3^d - 1)`

### R0R0 Entry (Even Numbers)

```
valid_R0R0_entry_number(d, n) = n·2^d
```

| Parameter | Meaning | Constraint |
|-----------|---------|------------|
| d | Depth (R0 count) | d ≥ 1 |
| n | Odd component | n ≥ 1, n odd |

**Output after R0^d**: `n`

---

## Canonical Chains

### Definition

```
canonical_chain(b, d) = 
  if b = true  then repeat_R1R0(d) ++ [R0]     [R1R0 entry]
  else              repeat_R0(d) ++ [R1; R0]   [R0R0 entry]
```

### R0 Advantage

| Chain Type | R0 Count | R1 Count | Advantage |
|------------|----------|----------|-----------|
| `canonical_chain(true, d)` | d + 1 | d | **1** |
| `canonical_chain(false, d)` | d + 1 | 1 | **d** |

---

## Macrostep

### Definition

A **macrostep** is a pair of canonical chains:
1. R0R0 chain: `canonical_chain(false, d₀)`
2. R1R0 chain: `canonical_chain(true, d₁)`

### Properties

| Property | Value |
|----------|-------|
| Chain count | 2 |
| R0 advantage | d₀ + 1 ≥ 2 |
| Mod 6 closure | Returns to mod 6 ≡ 2 |

---

## R0 Advantage

### Definition

```
R0 advantage = (# of R0 operations) - (# of R1 operations)
```

### Key Properties

1. **Additivity**: `advantage(seq1 ++ seq2) = advantage(seq1) + advantage(seq2)`
2. **Linear Growth**: After t macrosteps, advantage ≥ 2t
3. **Convergence Implication**: Positive advantage → shrinking tendency

---

## Mod 6 ≡ 2 Orbit

### Definition

Numbers m such that `m mod 6 = 2`: {2, 8, 14, 20, 26, 32, ...}

### Properties

| Property | Statement |
|----------|-----------|
| R1R0 output | Always ≡ 2 (mod 6) |
| Macrostep closure | Starts and ends in orbit |
| Advantage guarantee | Each macrostep contributes ≥ 2 |

---

## Key Functions

| Function | Signature | Description |
|----------|-----------|-------------|
| `sequence_end(m, ops)` | nat → list CollatzOp → nat | Final value after operations |
| `build_k_steps(m, k)` | nat → nat → list CollatzOp | Construct k canonical steps |
| `valid_sequence(ops, m)` | list CollatzOp → nat → Prop | Sequence validity predicate |
| `count_operations(seq)` | list CollatzOp → nat × nat | Returns (R0_count, R1_count) |
| `sum_contributions(chains)` | list → nat | Total R0 advantage |
| `chains_R0_advantage(chains)` | list → Prop | Advantage property |

---

## Notation Summary

| Symbol | Meaning |
|--------|---------|
| m, n | Positive integers |
| d, D | Depth parameters |
| k | Operation count |
| t | Macrostep iteration count |
| K | Prefix length to mod 6 ≡ 2 |
| ops | Operation sequence |
| chains | List of canonical chains |
| `^` | Exponentiation |
| `++` | List concatenation |
| `mod` | Modulo operation |

---

## Glossary

| Term | Definition |
|------|------------|
| **Canonical Chain** | Standardized operation sequence with known R0 advantage |
| **Entry Function** | Parametrized representation of Collatz entry points |
| **Macrostep** | Iteration unit on mod 6 ≡ 2 orbit |
| **R0 Advantage** | Difference between R0 and R1 operation counts |
| **Mod 6 ≡ 2 Orbit** | Strategic subset of integers with closure properties |
| **Pattern** | Repeated operation structure (R1R0 or R0R0) |
| **Depth (d)** | Number of pattern repetitions |
| **Closed Form** | Explicit algebraic expression for output |

---

## Quick Formulas

```
Entry Functions:
  R1R0: m = 2·2^d·n + (2^d - 1)
  R0R0: m = n·2^d

Output Closed Forms:
  R1R0^d: 2·3^d·n + (3^d - 1)
  R0^d: n

R0 Advantage:
  Single R1R0 chain: 1
  Single R0R0 chain: d
  Macrostep: d₀ + 1 ≥ 2
  t macrosteps: ≥ 2t

Operation Bounds:
  To mod 6 ≡ 2: k ≤ 2·(log₂ m + 1)
```
