---
numbersections: true
header-includes:
    - \usepackage{BOONDOX-calo}
    - \usepackage{dsfont}
---

# Database theory.

## Primary key/Foreign keys.

```sql
CREATE TABLE Reservation (
    client int ,
    room int ,
    arrival datetime ,
    PRIMARY KEY ( room , arrival ) ,
    FOREIGN KEY ( client ) REFERENCES Client ( id )
);
```

## Relational algebra.

Operations:

- $\langle j : d \rangle$ is “*tuple creation*”
- $R$, for $R \in \mathcal{R}$
- $\sigma_{j = d} {-}$ is *selection*
- $\pi_X {-}$ is *projection*
- $\rho_f {-}$ is *renaming*
- ${-}\bowtie{-}$ is *natural join*
- ${-}\cup{-}$ is *union*
- ${-}\setminus{-}$ is *difference*

Other operations:

- ${-}\div{-}$ is *division*: writing $\Delta := \mathsf{Att}_R \setminus \mathsf{Att}_S$,
  $$ R \div S := \{ u \in \pi_\Delta(R) \mid \forall s \in S, su \in R \} $$
- ${-}\ltimes{-}$ is *semi-join*, $R \ltimes S := \pi_{\mathsf{Att}_R} (R \bowtie S)$
- $\theta$-join is a join based on *in*equalities, *i.e.*\ $\sigma_{\text{condition}}(R \bowtie S)$

## First-order logic.

- **Semantics.** Given an assignment $\lambda : \mathrm{Vars} \to \mathrm{Domain}$, we write $I, \lambda \models \phi$.
- $[\![ \phi ]\!]^I := \{ \lambda : \mathrm{FreeVars}(\phi) \to \mathrm{Domain} \mid I, \lambda \models \phi \}$
- Query *evaluation* is **PSPACE**-complete (is $[\![ \phi ]\!]^I$ non-empty?)
- Query *containment* is **undecidable** (is $[\![ \phi ]\!]^I$ a subset of $[\![ \psi ]\!]^I$ for all $I$?)
- Query *equivalence* is **undecidable** (is $[\![ \phi ]\!]^I$ equal to $[\![ \psi ]\!]^I$ for all $I$?)
- *Satisfiability* (with finite model) is **undecidable** (Trakhenbrot's theorem).

- Domain independance is **undecidable**


## Codd's theorem.

Domain independent first-order logic is equivalent to relational algebra.

- From SPJRUD to FO, use $\exists$ as a mask.
- From FO to SPJRUD, we need to use the *active domain* $\mathsf{Adom}_x$:
    - $\lnot \phi \leadsto \prod_{x \in \mathrm{FreeVars}(\phi)} \mathsf{Adom}_x \setminus q_\phi$
    - $x = y \leadsto \sigma_{x = y} \mathsf{Adom}_x \bowtie \mathsf{Adom}_y$

    where $\mathsf{Adom}_x := \Big(\bigcup_{a \in \mathrm{adom}(\phi)} \langle x : a \rangle \Big) \cup \Big(\bigcup_{R \in \mathcal{R}} \bigcup_{u \in \mathsf{Att}_R} \pi_x \rho_{u \mapsto x} R\Big)$.


## Conjunctive queries.

Only use $\exists$ and $\land$ (no $\lor$, $\lnot$ nor $\forall$).
This corresponds to SPJR (no union and no difference, obviously).

We write these formulas with prefix $\exists$s (leaving them implicit).

All conjunctive queries are *domain independent* (if range-restricted) and *satisfiable* (with the *canonical database* $I[q]$).

**Range-restricted.** We allow “$x = y$” (with $x,y$ variables) in the query as long as we have $x$ or $y$ in some $R(\ldots)$.

General form is $q(\underbrace{y_1, \ldots, y_n}_{\text{head}}) := \underbrace{R_1(\vec{u}_1) \wedge \cdots \wedge R_m(\vec{u}_m)}_{\text{body}}$.

A *boolean* conjunctive query $q$ has no head variable (and thus $[\![ q ]\!]^I$ is either empty or singleton).

**Homomorphism theorem.** The three are equivalent:

+ query $q$ is contained in query $q'$;
+ there exists a homomorphism $h : q' \to q$;
    - $h : \mathrm{Vars}(q') \to \mathrm{Vars}(q) \cup \mathrm{Constants}(q)$
    - for all $R(\vec{u})$ in $q'$ there exists a $R(h(\vec{u}))$ in $q$
    - $h(\mathrm{HeadVars}(q')) = \mathrm{HeadVars}(q)$.
+ $\mathrm{HeadVars}(q)$ satisfies $q'$ in the canonical database $I[q]$.


Query evaluation and containment are **NP**-complete (by homomorphism theorem).


### *Acyclic* conjunctive queries.

With Yannakakis's algorithm, query evaluation is in **P**:

- Construct a *join-tree*
- Evaluate the query following the join-tree (using semijoins).

**Constructing the join-tree** (*Graham-Yu-Ozsoyoglu*)**.** Consider the hypergraph were hyperedges are exactly relations and vertices are $\mathrm{Vars}(q)$.
The idea is to remove *ears*. An *ear* $e$ is an hyperedge which is either isolated or has a face (a *face* $f$ is an hyperedge such that vertices $e \setminus f$ only occurs in $e$, like a face).

## Dependencies.

### Functional dependencies.

A *functional dependency* is an expression $R : X \to Y$ where $X, Y \subseteq \mathsf{Att}_R$, meaning $X$ *uniquely depends* on $Y$.

**Semantics.** We have $I \models R : X \to Y$ iff, for all $r, r' \in R^I$, if $r_{|\mathsf{Att}_X} = r_{|\mathsf{Att}_X}$ then $r_{|\mathsf{Att}_Y} = r_{|\mathsf{Att}_Y}$.


A *superkey* $K \subseteq \mathsf{Att}_R$ for $R$ is a functional dependency $R : K \to \mathsf{Att}_R$.
A *candidate key* is a superkey such that none of its proper subsets is a superkey.

**Armstrong’s axioms.**

$$
{\scriptstyle Y \subseteq X} \dfrac{}{X \to Y} \textit{reflexivity}
\qquad
\dfrac{X \to Y}{XZ \to YZ}\textit{augmentation}
$$
$$
\dfrac{X \to Y \quad Y \to Z}{X \to Z}\textit{transitivity}
$$
*extensions:*
$$
\dfrac{X \to Y \quad X \to Z}{X \to YZ}\textit{union}
\qquad
\dfrac{X \to YZ}{X \to Y}\textit{decomposition}
$$


The *closure* of $X$ under $\Sigma$ (set of functional dependencies) is
$$ \mathcal{Cl}_\Sigma(X) := \{ A \text{ attribute} \mid \Sigma \models X \to A \}. $$
It can be computed in linear-time.

**Boyce-Codd normal form.**
For all $X, Y \subseteq \mathsf{Att}_R$, if $\Sigma \models R : X \to Y$ then $Y \subseteq X$ or $X$ is superkey for $R$.

### Join dependencies.

A *join dependency* is an expression $R : {\bowtie}[X_1, \ldots, X_n]$.

**Semantics.**
$I \models R : {\bowtie}[X_1, \ldots, X_n]$ iff $R^I = \pi_{X_1}(R^I) \bowtie \cdots \bowtie \pi_{X_n}(R^I)$.


### Multi-Valued dependencies.

A *multi-valued dependency* is an expression $R : X \twoheadrightarrow Y$.
The meaning of a multi-valued dependency $R : X \twoheadrightarrow Y$ is a join-dependancy $R : {\bowtie}[XY, X\bar{Y}]$ where $\bar{Y} := \mathsf{Att}_R \setminus Y$.

**Important.** $I \models R : X \to Y$ implies $I \models R : X \twoheadrightarrow Y$.

Using Armstrong's rules, with the following four for mvd

$$
{\scriptstyle Y \subseteq X} \dfrac{}{X \twoheadrightarrow Y} \textit{reflexivity}
\qquad
\dfrac{X \twoheadrightarrow Y}{XZ \twoheadrightarrow YZ}\textit{augmentation}
$$
$$
\dfrac{X \twoheadrightarrow Y}{X \twoheadrightarrow \bar Y}\textit{“symmetry”}
\qquad
\dfrac{X \twoheadrightarrow Y \quad Y \twoheadrightarrow Z}{X \twoheadrightarrow Z \setminus Y}\textit{transitivity}
$$

and the following two for mvd $\leftrightarrow$ fd:

$$
\dfrac{X \to Y}{X \twoheadrightarrow Y}
\qquad
\dfrac{X \twoheadrightarrow Y \quad XY \twoheadrightarrow Z}{X \to Z \setminus Y}
$$

we obtain a **sound and complete** axiomatization.

### Chase algorithm.

- Start with a table containing two tuples with all different values;
- when considering hypothesis $A \to BC$, we will *add equalities*: if two tuples have the same $X$-values, then make their $Z$-values equal;
- when considering hypothesis $X \twoheadrightarrow Z$, we will *add tuples*: if two tuples have the same $X$-values, then add two copies of these two tuples and exchange their $Z$-values.


## Recursive queries.

```sql
WITH RECURSIVE T( x1 , ... , xn ) AS (
    SELECT -- < base case query >
UNION
    SELECT -- < inductive case query using T >
)
SELECT * FROM T ;
```

This uses algorithms to compute a fixed-point (we should consider a *monotone* map $F : \mathbf{2}^{\mathcal{U}} \to \mathbf{2}^{\mathcal{U}}$).
In that case, the "trivial" fixed-point algorithm always terminates (for finite $\mathcal{U}$) and returns $\mathsf{lfp}(F)$.


- *Semipositive Datalog*: monotone so $\checkmark$
- *Datalog$^\lnot$*: non-monotone but we can use *inflationary semantics* so $\checkmark$
- *Datalog$^{\lnot\lnot}$*: partial fixed-points.


Equivalence between Datalog$^\lnot$ and infl.\ while programs.
These programs have the form

> "while something changed, do ... $\cup=$ ... (a few times)".

**Main results.**

- $\mathsf{FO[LFP,<]} = \mathsf{FO[LFP,<]} = \mathbf{P}$.
- $\mathsf{FO[PFP,<]} = \mathbf{PSPACE}$.

## Size of joins.

**AGM bound.** Let $q$ a full CQ. For all fractional edge covers $u$ of $G(q)$, we have:
$$ \# [\![q]\!]^I \leq \prod_{R(\vec{x}) \in \mathsf{body}(q)} (\# R^I)^{u(R(\vec{x}))}. $$

A *fractional edge cover* of an hypergraph $(E, V)$ is $u : E \to \mathds{R}^+$ such that, for all $x \in V$,
$$ \sum_{e \ni x} u(e) \geq 1. $$


## Provenance.

Fix $K$ a *semiring*.
A $K$-relation is a map $R : \mathrm{Domain}^{\mathsf{Att}_R} \to K$ whose support is finite (only finite non-zero values).

Provenance is inductively defined by

- $\displaystyle\mathsf{Prov}(\emptyset) := t \mapsto 0$.
- $\displaystyle\mathsf{Prov}(q \cup q') := t \mapsto \mathsf{Prov}(q)(t) + \mathsf{Prov}(q')(t)$.
- $\displaystyle\mathsf{Prov}(\sigma_P q) := t \mapsto \begin{cases}
\mathsf{Prov}(q)(t) & \text{if predicate $P(t)$ holds}\\
0 & \text{otherwise}
\end{cases}$.
- $\displaystyle\mathsf{Prov}(\pi_A q) := t \mapsto \sum_{t' \text{ st } t'_{|A} = t^{\phantom{\prime}}_{|A}} \mathsf{Prov}(q)(t)$.
- $\displaystyle\mathsf{Prov}(q \bowtie q') := t \mapsto \mathsf{Prov}(q)(t_{|\mathsf{Att}_q}) \times  \mathsf{Prov}(q')(t_{|\mathsf{Att}_{q'}})$
- $\displaystyle\mathsf{Prov}(q \setminus q') := t \mapsto \mathsf{Prov}(q)(t) - \mathsf{Prov}(q')(t)$



# Data Mining.

![Everything in one figure](dm/dm.png)

**Vocabulary.** data set, data object, attribute/dimension/feature/variable (nominal, binary, ordinal, quantity, interval, ratio, discrete, continuous).


- Measuring the Central Tendency: mean, median, mode (most frequent value)
- Measures Data Distribution: 
    - Variance/Standard Deviation,
    - Covariance ($\sigma_{1,2} = \mathds{E}[X_1 X_2] - \mu_1 \mu_2$, ***warning*** $\sigma_{1,1} = \sigma_1^2$) $\leadsto$ *covariance matrix*,
    - $\chi^2 = \sum_i \sum_j (o_{i,j} - e_{i,j})^2 / e_{i,j}$ where $o_{i,j}$ is the *observed* $\#(A_i, B_j)$ and $e_{i,j}$ is the *expected* $\# A_i \times \# B_j / n$,
    - Correlation $\rho_{i,j} = \sigma_{i,j} / \sigma_i \sigma_j$
    - Dissimilarity matrix $(\mathsf{dist}(\vec{x}_i, \vec{x}_j))_{i,j \in [\![1, n ]\!]}$, requires a meaningful distance $\mathsf{dist}(\cdot, \cdot)$ (*e.g.*\ the Minkowski distance for numeric data)
    - $z$-score: $z = (x - \mu) / \sigma$.

- Graphic Displays of Basic Statistical Descriptions: Boxplot, Histogram, Quantile plot, Quantile-quantile (q-q) plot, Scatter plot.

A **document** is a matrix $\mathrm{labels} \times \mathrm{frequencies}$.

**KL** (Kullback-Leibler) **Divergence.** Comparing Two Probability Distributions.

$$ D_{\mathrm{KL}}(p || q) = \sum_{x \in \mathcal{X}} p(x) \ln \left( \frac{p(x)}{q(x)} \right). $$

*"How many bits should I add to $q(\cdot)$ to obtain $p(\cdot)$?"*


## Data preprocessing.

+ Data cleaning (*e.g.*\ removing outliers, dealing with missing data)
+ Data integration (*e.g.*\ data cubes)
+ Data reduction (*e.g.*\ dimensionality reduction, data compression, ***sampling***)
+ Data transformation and data discretization (*e.g.*\ normalization).

### Data cleaning.

- How to Handle Missing Data? Use the most probable value.
- How to Handle Noisy Data? Binning, Regression, Clustering, Semi-supervised


### Data transformation.

- Normalization: min-max normalization, $z$-score normalization, decimal scaling $x' = x / 10^j$.
- Discretization: binning, histogram, clustering, decision-tree (supervised), correlation.

## Data Warehouse.

- **OLTP.** "Analysis while the data is collecting"
- **OLAP.** "Analysis after the data is collected"

We should use a data warehouse for **OLAP**, not **OLTP**.

**"Usual" operations.** Sort, summarize, consolidate, compute views, check integrity, and build indices and partitions.

Refresh: propagate the updates from the data sources to the warehouse

A *data lake* is a centralized repository storing all structured and unstructured data at any scale in an organization. Everything in one place, stored "as is", no analysis.

## Data cubes.

Data that can be viewed in multiple dimensions:

- a set of tables for *dimensions* (one "side" of a cube)
- a table of *facts* (~ raw data)

An $n$-dimensional base cube is called a *cuboid*.
All cuboids form a *lattice*.

A few schema: *star* schema, *snowflake* schema, *fact constellation*.

**Data Cube Measures.**

- *Distributive*: apply to groups and compare with global.
- *Algebraic*: computed by an algebraic function.
- *Holistic*: ***no idea***


**Operations.**

- *Roll up (drill-up)*: summarize data by climbing up hierarchy or by dimension reduction
- *Drill down (roll down)*: reverse of roll-up, from higher level summary to lower level summary or detailed data, or introducing new dimensions


**Iceberg cube.** Compute only the cells whose measure satisfies the iceberg condition (some condition to filter)


## Pattern mining.

Pattern discovery $\leadsto$ classification, clustering.

A $k$-itemset is an itemset with $k$ items.
Absolute Support: number of occurrences.
Relative Support: probability.

**Downward closure (also called "*apriori*"):** any subset of a frequent itemset must be frequent

How to compute frequent $k$-itemsets:

- Scan DB once to get frequent $1$-itemset
- While no frequent or candidate set can be generated do
    - Generate length-$(k+1)$ candidate itemsets from length-$k$ frequent itemsets
    - Test the candidates against DB to find frequent $(k+1)$-itemsets
    - Increase $k$


**FP-trees** (FP means frequent patterns)**.** Allow for divide and conquer.

- Supervised learning (classification, numeric prediction): we give labels
- Unsupervised learning (clustering): labels are unknown

## Supervised Classification.

**Bayes' theorem.**
$$ \underbrace{\Pr[H \mid X]}_{\text{posteriori}} \propto \underbrace{\Pr[X \mid H]}_{\text{likelyhood}} \times \underbrace{\Pr[H]}_{\text{prior}} $$

Classification is to derive the maximum posteriori. We use "likelyhood tables."

Decision trees induced by the data (ID3): at each node we try to maximize the *information gain*.
For *continuous values*, use **best split point**.
They are easy to explain, implement, officiant but lack stability as they tend to overfit the data.

**Lazy/eager learners.**

- *lazy*: no preprocessing, full algorithm at runtime (*e.g.*\ $k$-NN);
- *eager*: preprocessing and minimal algorithm at runtime.

**Confusion matrix.** True/false positive/negative.

## Clustering.

- Essential Measures of Cluster:
    + **Centroid.** $\mathrm{centroid}(C) = \operatorname{avg} C$
    + **Radius.** $\displaystyle \mathrm{radius}(C) = \sqrt{\operatorname{avg}_{x \in C} \mathsf{dist}(x, \operatorname{avg} C)^2}$
    + **Diameter.** $\displaystyle \mathrm{diameter}(C) = \sqrt{\operatorname{avg}_{x \neq x'\in C} \mathsf{dist}(x, x')^2}$

### $k$-means.

Complexity in $\mathrm{O}(tkn)$ for $t$ iterations and $n$ elements, usually $k, t \ll n$.

Cons:

- Usually stuck on a local optimum,
- $k$ needs to be specified correctly,
- sensitive to noise and outliers,
- only for *continuous* attributes in convex spaces.

**Improvement: $k$-means`++`.**
Initialize one centroid at a time, choosing the furthest one from all (already initialized) others at each step.


**Improvement: $k$-medoids.**
Instead of mean use medioid in the iteration loop.
Pick a random point non-repr, and compute the cost of swapping representative; swap if the cost is negative.
Complexity in $\mathrm{O}(k(n-k)^2)$.

**Random empirical value.**
Pick $k$ around $\sqrt{n / 2}$.

### Agglomerative Clustering.

- Single link (nearest neighbor) $\leadsto \mathrm{sim}(C, C') = \min_{(x, x') \in C \times C'} \mathrm{sim}(x, x')$
- Complete link (diameter) $\leadsto \mathrm{sim}(C, C') = \max_{(x, x') \in C \times C'} \mathrm{sim}(x, x')$
- Average link (group average) $\leadsto \mathrm{sim}(C, C') = \operatorname{avg}_{(x, x') \in C \times C'} \mathrm{sim}(x, x')$
- Centroid link (centroid similarity) $\leadsto \mathrm{sim}(C, C') = \mathrm{sim}(\operatorname{avg} C,  \operatorname{avg} C')$.


### BIRCH: A Multi-Phase Hierarchical Clustering Method.

- **Phase 1.** Build a CF (clustering feature) Tree.
- **Phase 2.** Arbitrary algorithm to cluster the leaf nodes of the tree.

Building the CF tree is based on

> For each point in the input,
>
> - Find its closest leaf entry
> - Add point to leaf entry and update CF
> - If entry diameter > `max_diameter` then split leaf, and possibly parents

Lead to unnatural clusters as we fix the *size* of each cluster not the number of clusters.

**Random empirical value.**
Pick $\sqrt{2n}$ for the maximum size of each cluster.


### DBSCAN: Density-Reachable and Density-Connected.

A cluster is defined as a maximal set of density-connected points.
Two parameters:

- radius $\varepsilon$ of neighborhood
- minimum number of points on the neighborhood
- $\mathrm{neighborhood}(x) := \{ y \in \mathcal{D} \mid \mathsf{dist}(x, y) \leq \varepsilon \}$.

Complexity in $\mathrm{O}(n^2)$ (or $\mathrm{O}(n \log n)$ if spatial index).

### OPTICS: Ordering Points To Identify Clustering Structure.

Extension of *DBSCAN*.

**Idea.** Higher density points should be processed first; find high-density clusters first.

Same complexity.

### Grid-based Clustering Methods.

- **STING: STatistical INformation Grid approach.** Different levels of resolution, like a CF-tree.

- **CLIQUE.** Find dense regions (clusters) in each subspace; use the apriori principle: a 2D region can't be dense if its projection is not.
