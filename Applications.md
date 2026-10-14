# Quantitative applications

Use the notation and indexing of [Proof.md](Proof.md): the triple is
$(\Theta_n,\Theta_{n+1},\Theta_{n+2})$, with central digit $a_{n+2}=a$,
finite past $x=q_n/q_{n+1}$, and infinite future
$y=[0;a_{n+3},a_{n+4},\ldots]$.

## Localization from a measured deficit

For real $a\ge2$ and $x,y\in[0,1]$, set $D=c_a-F_a(x,y)$.
The sharp inverse theorem gives

```math
\max\{|x-\beta_a|,|y-\beta_a|\}\le D/\kappa_a.
```

Thus $F_a(x,y)\ge c_a-\epsilon$ places both coordinates in
$[\beta_a-\epsilon/\kappa_a,\beta_a+\epsilon/\kappa_a]$.
The coefficient is uniform over the full square and is optimal.
Actual irrational triples satisfy the inverse estimate strictly.

More generally, for $L<\beta_a<U$, the condition

```math
D<\kappa_a\min\{\beta_a-L,U-\beta_a\}
```

puts both coordinates in $(L,U)$. This transfers a deficit in three
approximation coefficients into information about each tail separately.

For a measured maximum excess $E=G_a(x,y)-c_a$, the maximum inverse
estimate similarly gives

```math
\max\{|x-\beta_a|,|y-\beta_a|\}\le E/\lambda_a,
\qquad \lambda_a=\frac{a\beta_a}{a^2+4}.
```

Its coefficient is optimal on the square and on actual triples. The
inequality is strict on actual triples, and equality on the square
occurs only at the metallic point.

## A small deficit forces an actual constant-digit window

Let $a\ge2$ be an integer and $r\ge0$. Sort the endpoints of
$K_r=T_a^r([0,1])$ as $L_r<U_r$ and define

```math
\delta_r=\min\{\beta_a-L_r,U_r-\beta_a\}>0.
```

For every irrational input with central digit $a_{n+2}=a$, if

```math
c_a-\min(\Theta_n,\Theta_{n+1},\Theta_{n+2})
 <\kappa_a\delta_r,
```

then

```math
r<n+1\ \text{(equivalently }r\le n\text{)},\qquad
a_{n+1-i}=a\ (0\le i<r),\qquad
a_{n+3+i}=a\ (0\le i<r).                              \tag{1}
```

This is a statement about the actual floor/fraction digits, including
the finite-past length condition. The inverse estimate first puts both
tails in the interior of $K_r$. Since
$T_a((0,1))=(1/(a+1),1/a)$, the unique first positive digit there is
$a$, with an interior remainder. Repeated inversion recovers the asserted
window. A past exhausted at or before the end of that window cannot have such
an interior remainder. The literal reversed finite expansion, including terminal
ones, is retained.

The threshold uses exact rational cylinder endpoints and the metallic
root. This is a convenient sufficient threshold. The exact optimal cutoffs
below strengthen it for each specified window. With the continuants in Proof.md (4), it also
has the explicit algebraic form

```math
\delta_r=
\frac1{P_r\beta_a+P_{r+1}}
\min\left\{\frac{\beta_a}{P_{r+1}},
            \frac{1-\beta_a}{P_r+P_{r+1}}\right\}.       \tag{2}
```

Indeed, subtract $T_a^r(\beta_a)=\beta_a$ from the fractional-linear
formula to obtain

```math
|T_a^r(t)-\beta_a|
=\frac{|t-\beta_a|}
 {(P_rt+P_{r+1})(P_r\beta_a+P_{r+1})}.
```

Evaluating at $t=0,1$ gives (2). The Lean digit-window contract uses the
sorted iterated endpoints directly.

## Optimal cutoffs for a prescribed digit window

For $0\le L<\beta_a<U\le1$, define the exact rational-profile cutoffs

```math
B_F(L,U)=\max\{\phi_a(L),\phi_a(U)\},\qquad
B_G(L,U)=\min\{\psi_a(L),\psi_a(U)\}.
```

Outside $(L,U)^2$, the largest possible minimum is $B_F$ and the smallest
possible maximum is $B_G$. Both values are attained on the closed square:
a coordinate equals an endpoint selecting the cutoff, and the other is
the profile witness in Proof.md. The side monotonicities show that every
point farther outside satisfies the corresponding bound. Thus either
$F_a(x,y)>B_F$ or $G_a(x,y)<B_G$ forces both coordinates into $(L,U)$.
For different past and future intervals, use the maximum of the four
lower-profile endpoint values and the minimum of the four upper-profile
endpoint values. The same proof gives exact complement extrema.

Take $[L,U]=K_r$, where $r\ge1$. For actual irrational triples with integer
central digit $a\ge2$, either test forces exactly the window conclusion
(1), including $r\le n$. These are optimal numerical cutoffs even over
actual triples, allowing the finite index to vary: for every
$\epsilon>0$ there is a triple with a future digit violating the required
window and minimum greater than $B_F-\epsilon$; another has maximum less
than $B_G+\epsilon$.

To see this, choose the boundary endpoint and profile witness attaining
the relevant cutoff. Approach that endpoint by irrational future
coordinates from outside $K_r$, while positive rational pasts approach
the other coordinate. Finite-word realization yields actual triples;
continuity gives the objective limit. A future outside $K_r$ cannot have
its first $r$ digits all equal to $a$. This construction also avoids
any ambiguity in rational finite endpoint expansions.

The exact silver cutoffs are:

| Required digits on each side | Cylinder $K_r$ | Minimum must exceed $B_F$ | Maximum must be below $B_G$ |
| --- | --- | --- | --- |
| $r=1$ | $[1/3,1/2]$ | $10/29$ | $21/58$ |
| $r=2$ | $[2/5,3/7]$ | $119/338$ | $60/169$ |
| $r=3$ | $[7/17,5/12]$ | $348/985$ | $697/1970$ |

The actual extraction theorem also permits different past and future
lengths $r,s$, using their four endpoint values; only the past requires
$r\le n$. The varying-index actual optimality statement above concerns
the symmetric window $r=s$.

## Effective convergence of all run constants

For real $a>1$, $T_a$ is $a^{-2}$-Lipschitz on $[0,1]$. Every point in
$I_r^e$ is therefore within $a^{-2r}$ of $\beta_a$. For $a\ge1$ the
two envelopes satisfy, on nonnegative coordinates,

```math
|F_a(x,y)-F_a(u,v)|\le|x-u|+|y-v|,\qquad
|G_a(x,y)-G_a(u,v)|\le|x-u|+|y-v|.
```

Each side fraction has this bound by positive-denominator differences;
the central fraction does as well. Taking a finite minimum or maximum
preserves it. Applying the estimate at the extremizing corners gives

```math
0<c_a-C_{a;r,s}^{e,f}\le a^{-2r}+a^{-2s},\qquad
0<U_{a;r,s}^{e,f}-c_a\le a^{-2r}+a^{-2s}.               \tag{3}
```

Both sharp constants thus converge to the classical threshold as both
run lengths grow. These rates are proved bounds and are not claimed to
be optimal. Exact interval widths follow from the continuant identity:

```math
|T_a^r(v)-T_a^r(u)|
=\frac{v-u}{(P_ru+P_{r+1})(P_rv+P_{r+1})}\qquad(0\le u<v\le1).
```

A more precise two-sided estimate uses the actual endpoint distances.
For a terminated run cell $I_r^e=[\ell_r^e,u_r^e]$, put

```math
d_r^e=\min\{|\ell_r^e-\beta_a|,|u_r^e-\beta_a|\},\qquad
E_r^e=\max\{|\ell_r^e-\beta_a|,|u_r^e-\beta_a|\}.
```

The cell lies wholly on one side of $\beta_a$, so every point in it has
distance between these values. Applying the two sharp stability
inequalities and the Lipschitz estimates at the optimizing corners gives

```math
\kappa_a\max\{d_r^e,d_s^f\}
 \le c_a-C_{a;r,s}^{e,f}\le E_r^e+E_s^f,
```

```math
\lambda_a\max\{d_r^e,d_s^f\}
 \le U_{a;r,s}^{e,f}-c_a\le E_r^e+E_s^f.
```

These hold for every real $a\ge2$, both departure sides, and all finite
run lengths. They provide positive lower bounds as well as effective
upper bounds for each gap.

## Exact regions for near extremizers

For $0<t<a$ and nonnegative $x,y$, let
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

Intersect with a prescribed cylinder rectangle. Taking
$t=C(R)-\epsilon>0$ describes exactly the lower-envelope values within
$\epsilon$ of the supremum. Taking $t=U(R)+\epsilon<a$ gives the
upper-envelope sublevel region. These equivalences include degenerate
rectangles. The separate maximum inverse estimate supplies its optimal
uniform linear coefficient.

## Fixed words and boundary attainability

A nonempty positive chronological word $w$ fixes the past
$x=[0;w^{\mathrm{rev}}]$ and the index $|w|-1$. The rectangle formulas
apply with this singleton first interval. For any terminated future run
class, irrational inputs preserving the whole word approach both sharp
constants at that same index. The optimizing future coordinates are
rational, so neither bound is attained by an actual irrational future.

An infinite all-$a$ future behaves differently: its coordinate is
$\beta_a$, and the endpoint examples in Proof.md attain the corresponding
terminated-past bounds. The exhausted all-$a$ past, the infinite constant
future, and the fully constant input are treated separately in the formal
statements.

The generic rectangle theorem also applies geometrically to
rational-endpoint cylinders produced by arbitrary finite digit words.
Boundary intersections, as well as corners, can be necessary. The actual
fixed-word sharpness contracts in this package specify a constant-digit
future run and its departure side.
