# The problem

Let $G$ be a finitely generated discrete group. Fix a finite symmetric
generating set $S$ containing the identity, and write
$$
B(n)=S^n,\qquad V(n)=|B(n)|,\qquad
|g|=\min\{n:g\in B(n)\}.
$$
Adding the identity makes these powers the closed word balls.

The group has **polynomial growth** if $V(n)\le C(n+1)^d$ for some
natural numbers $C,d$ and all $n$. It has **subexponential growth** if
$$
\lim_{n\to\infty}\frac{\log V(n)}n=0.
$$
A group is **virtually nilpotent** if it has a nilpotent subgroup of finite
index. Its equivalence with polynomial growth is a standard input,
attributed to Gromov and the classical growth theory of nilpotent groups.
See [REFERENCES.md](REFERENCES.md).

## Cross sections and recurrence

For a Borel action $G\curvearrowright X$ on a standard Borel space, put
$$
d(x,y)=\min\{|g|:g\cdot x=y\}
$$
within each orbit, with distance infinity between distinct orbits.
A **cross section** is a Borel subset meeting every orbit.

A set $C$ is **$r$-separated** if $d(c,c')>r$ for distinct points
of $C$. Maximality means maximality among all separated supersets,
including non-Borel supersets. A maximal $r$-separated set meets every
orbit, and every point has distance at most $r$ from it.

For positive integers $r_0<r_1<\cdots$, a sequence of $r_n$-separated
cross sections $C_n$ is **recurrent** if
$$
\forall x\in X\ \forall\varepsilon>0\ \forall N\
\exists n\ge N:\quad d(x,C_n)<\varepsilon r_n.
$$
This is everywhere infinitely-often recurrence, equivalently
$\liminf_n d(x,C_n)/r_n=0$ for every $x$.

Lean expresses the distance inequality by witnesses $c\in C_n$ and
$g\in G$ with $g\cdot c=x$ and $|g|<\varepsilon r_n$.
It is the same condition for actions with stabilizers.

## Background and motivating question

Boykin and Jackson constructed recurrent sections for free Borel
$\mathbb Z^d$-actions. The formulation in Marks and Unger's
*Borel circle squaring*, Appendix A, Lemma A.2, gives recurrent maximal
sections at every prescribed increasing integer schedule. Their discussion
suggests an extension to nilpotent groups and raises a broader amenable-group
question. Such sections are useful in constructions of hyperfinite
orbit equivalence relations.

The motivating question is:

> Which finitely generated groups admit recurrent separated Borel
> cross sections in every Borel action, for every prescribed increasing
> positive integer radius sequence?

The [characterization](RESULTS.md) identifies polynomial growth,
equivalently virtual nilpotence, subject to the explicit standard inputs
of the formal theorem. The positive proof extends the lattice mechanism
using compact models of rescaled word balls and finite Borel coloring.
It includes nonfree actions. The earlier constructions and geometric/Borel
tools are credited in [REFERENCES.md](REFERENCES.md); this repository
makes no definitive publication-priority claim.

## The order of quantifiers

Two properties are different:

1. **Prescribed radii:** for every action and every increasing positive
   integer schedule $r$, there is a recurrent sequence $C$.
2. **Existential radii:** for every action, there is some increasing
   positive integer schedule $r$ and a recurrent sequence $C$.
   Here $r$ may depend on the action.

The first property forces polynomial growth. The checked obstruction for
the second forces subexponential growth. The code does not prove these
properties equivalent or assert sufficiency of subexponential growth.

Strict increase of integer radii implies $r_n\ge n$, supplying the
summability used in the single-sequence obstruction. No corresponding
claim is made for arbitrary increasing real radii.

## The free probability-preserving test action

For growth obstructions, one action that is free and preserves a probability
measure suffices. Freeness makes suitable translates of a separated set
disjoint; invariance and total mass one give neighborhood-measure bounds.

Every countable group has such an action: restrict the Bernoulli shift on
$[0,1]^G$ to its invariant conull free part. This existence result is
an explicit input when passing from a universal Borel-action hypothesis
to a group conclusion. The fixed-action theorems already assume the action.

Those hypotheses matter. The transitive action of an infinite group on
itself has a recurrent constant singleton section along any radii tending
to infinity, whatever the group growth. That action has no invariant
probability measure.

This repository formalizes the discrete word-metric results in
[RESULTS.md](RESULTS.md), not a hyperfiniteness theorem or the locally
compact group version.
