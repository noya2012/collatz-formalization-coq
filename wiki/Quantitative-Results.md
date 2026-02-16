# Quantitative Results - Formulas and Bounds

## Core Formulas

### Entry Functions

| Type | Formula | Parameters |
|------|---------|------------|
| R1R0 Entry | `valid_R1R0_entry_number(d,n) = 2·2^d·n + (2^d - 1)` | d ≥ 1, n ≥ 0 |
| R0R0 Entry | `valid_R0R0_entry_number(d,n) = n·2^d` | d ≥ 1, n ≥ 1, n odd |

---

## Output Closed Forms

### R1R0 Pattern

```
sequence_end(valid_R1R0_entry_number(D,n), repeat_R1R0(D)) = 2·3^D·n + (3^D - 1)
```

### R0R0 Pattern

```
sequence_end(valid_R0R0_entry_number(D,n), repeat_R0(D)) = n
```

---

## Bounds Summary

### R1R0 Triple Bounds

```
max(2·3^D·n, 3^D - 1) ≤ output ≤ 3^D·(2n + 1)
```

| Component | Bound |
|-----------|-------|
| Lower bound 1 | 2·3^D·n |
| Lower bound 2 | 3^D - 1 |
| Upper bound | 3^D·(2n + 1) |

### R0R0 Bounds

```
1 ≤ n ≤ m
output = n (exact)
```

---

## R0 Advantage Formulas

### Single Chain

| Chain Type | R0 Count | R1 Count | Advantage |
|------------|----------|----------|-----------|
| R1R0 entry (d) | d + 1 | d | **1** |
| R0R0 entry (d) | d + 1 | 1 | **d** |

### Chain Concatenation

```
advantage(chain1 ++ chain2) = advantage(chain1) + advantage(chain2)
```

### Macrostep (2 chains)

```
advantage = d₀ + 1 ≥ 2
```

where d₀ ≥ 1 is the depth parameter of the R0R0 chain.

---

## Growth Rate Comparison

### Operation Count to Mod 6 ≡ 2

```
k ≤ 2·(log₂ m + 1)
```

| Input m | Max Operations |
|---------|----------------|
| 10 | 8 |
| 100 | 14 |
| 1000 | 20 |
| 10^6 | 42 |

### R0 Advantage Growth

```
After t macrosteps: advantage ≥ 2t
```

| Macrosteps t | Min Advantage |
|--------------|---------------|
| 1 | 2 |
| 10 | 20 |
| 100 | 200 |
| 1000 | 2000 |

### Key Comparison

| Quantity | Growth | As t → ∞ |
|----------|--------|----------|
| Operations (prefix) | O(log m) | Bounded |
| R0 Advantage | ≥ 2t | Unbounded |

---

## Power Condition (Convergence Path)

### Diophantine Characterization

R1R0 output is a power of 2 if and only if:

```
2^k + 1 = 3^d·(2n + 1)
```

This converts "convergence to power of 2" into an explicit Diophantine equation.

---

## Mod 6 Properties

### R1R0 Output Mod 6

```
sequence_end(valid_R1R0_entry_number(d,n), repeat_R1R0(d)) mod 6 = 2
```

**Always!** This is the foundation of the mod 6 ≡ 2 orbit.

---

## Canonical Representation Uniqueness

### Theorem

Every positive integer m has a **unique** canonical representation:

| m odd | Unique (d, n) with m = valid_R1R0_entry_number(d, n) |
| m even | Unique (d, n) with m = valid_R0R0_entry_number(d, n), n odd |

This uniqueness enables precise counting and algebraic manipulation.

---

## Summary Table

| Theorem | Formula | Significance |
|---------|---------|--------------|
| R1R0 Closed Form | `2·3^D·n + (3^D - 1)` | Exponential growth in D |
| R0R0 Exact Output | `n` | Linear simplicity |
| R0 Advantage | `d₀ + 1 ≥ 2` per macrostep | Linear growth guarantee |
| Operation Bound | `≤ 2·(log₂ m + 1)` | Logarithmic efficiency |
| Mod 6 Invariant | `≡ 2` | Orbit closure |

---

> 🔬 **[Interactive Visualization](cz_ms_cc_visualization)**: Explore these formulas on real Collatz sequences with live statistics
