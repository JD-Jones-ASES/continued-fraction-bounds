# Quantitative applications

Use the notation of [Proof.md](Proof.md). All statements below concern
ordinary continued fractions or their explicitly defined tail coordinates.
The exact list of Lean contracts is recorded in [Verification.md](Verification.md).

## Localization from a measured deficit

For real $a\ge2$ and $x,y\in[0,1]$, put
$D=c_a-F_a(x,y)$. The sharp inverse theorem gives

```math
\max\{|x-\beta_a|,|y-\beta_a|\}\le D/\kappa_a.
```

In particular, $F_a(x,y)\ge c_a-\epsilon$ implies that both coordinates
lie in the closed interval
$[\beta_a-\epsilon/\kappa_a,\beta_a+\epsilon/\kappa_a]$.
The constant is uniform over the unit square and every integer central digit.
For actual irrational inputs the inequality in the inverse theorem is strict.

More generally, suppose $L<\beta_a<U$ and
$D<\kappa_a\min\{\beta_a-L,U-\beta_a\}$.
Then both $x$ and $y$ belong to $(L,U)$. This gives an effective way to
infer digit information from three approximation coefficients.

## A small deficit forces a long constant-digit window

Let $a\ge2$ be an integer and $r\ge0$. Sort the endpoints of
$K_r=T_a^r([0,1])$ as $L_r<U_r$, and define

```math
\delta_r=\min\{\beta_a-L_r,U_r-\beta_a\}>0.
```

For an actual triple with central digit $a$, if

```math
c_a-\min(\Theta_{n-1},\Theta_n,\Theta_{n+1})
 <\kappa_a\delta_r,
```

then the $r$ digits immediately before and the $r$ digits immediately
after the central digit are all $a$. In particular $n\ge r$.

Indeed, the inverse theorem places both coordinates in the interior of
$K_r$. The open interval $T_a((0,1))=(1/(a+1),1/a)$ consists precisely
of tails whose first digit is $a$ and whose remainder is in $(0,1)$.
Repeatedly invert $T_a$ to recover $r$ such digits. A finite tail that
exhausts earlier has remainder zero and lies on a boundary, so cannot
occur under the strict deficit condition. The reversed finite expansion
is used as actually given; no canonicalization at a terminal digit $1$
is imposed.

The threshold is explicit. With the continuants from (4),

```math
\delta_r=
\frac1{P_r\beta_a+P_{r+1}}
\min\left\{\frac{\beta_a}{P_{r+1}},
            \frac{1-\beta_a}{P_r+P_{r+1}}\right\}.       \tag{7}
```

To verify (7), subtract $T_a^r(\beta_a)=\beta_a$ from (4) and use
the determinant of the fractional-linear map:

```math
|T_a^r(t)-\beta_a|
=\frac{|t-\beta_a|}
 {(P_rt+P_{r+1})(P_r\beta_a+P_{r+1})}.
```

Evaluate at $t=0,1$ and take the smaller endpoint distance. The
localization criterion is sufficient; optimal thresholds for each fixed
window are not claimed.

## Effective convergence of all run constants

The map $T_a$ is $a^{-2}$-Lipschitz on $[0,1]$. Hence every point in
$I_r^e$ is within $a^{-2r}$ of $\beta_a$. Each fraction in (1) is
1-Lipschitz in each coordinate, so its minimum and maximum are
1-Lipschitz for the sum metric. Therefore

```math
0<c_a-C_{a;r,s}^{e,f}\le a^{-2r}+a^{-2s},\qquad
0<U_{a;r,s}^{e,f}-c_a\le a^{-2r}+a^{-2s}.               \tag{8}
```

These estimates prove convergence without a numerical extrapolation.
They are not claimed to have optimal rates. Exact interval widths are
available from the same continuant identity:

```math
|T_a^r(v)-T_a^r(u)|
=\frac{v-u}{(P_ru+P_{r+1})(P_rv+P_{r+1})}\quad(u<v).
```

## Exact regions for near extremizers

For $0<t<a$ and nonnegative $x,y$, define
$H_t(z)=t(a+z)/(a+z-t)$. Clearing positive denominators gives

```math
F_a(x,y)\ge t
\iff x+y\le1/t-a,\quad x\ge H_t(y),\quad y\ge H_t(x),
```

and

```math
G_a(x,y)\le t
\iff x+y\ge1/t-a,\quad x\le H_t(y),\quad y\le H_t(x).
```

Intersect these regions with any prescribed cylinder rectangle. Taking
$t=C(R)-\epsilon>0$ gives exactly the points within $\epsilon$ of
the lower-envelope supremum. Taking $t=U(R)+\epsilon<a$ gives the
corresponding upper-envelope sublevel region. These are exact geometric
descriptions, including degenerate cylinders.

## Fixed pasts and finite digit words

The rectangle formulas accept arbitrary rational-endpoint cylinders,
not just constant-digit runs. A prescribed finite word defines an
iterated fractional-linear image of $[0,1]$. A fully fixed finite past
defines a singleton first interval. The resulting sharp constants use
boundary intersections as well as corners when necessary.

If the fixed positive past is rational, both optimizing future
coordinates are rational. An irrational future cannot attain them, but
approaches them through admissible digit strings. In contrast, an
infinite all-$a$ future has coordinate $\beta_a$ and permits the
attained endpoint examples described in Proof.md.
