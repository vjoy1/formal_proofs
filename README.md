# Formalizing Foundational Theorems in LEAN

This project explores the formal verification of mathematical theorems using the **LEAN 4 proof assistant**. The goal is to take well-known, foundational results from linear algebra and measure theory and translate their proofs into a machine-checkable format. This process not only guarantees the correctness of the arguments but also exposes the logical subtleties and foundational details that are often abstracted away in informal proofs.

The project consists of two independent formalizations:

1.  The **Steinitz Exchange Lemma**, a cornerstone of linear algebra that underpins the concept of a basis.
2.  The **Lebesgue Dominated Convergence Theorem (LDCT)**, a powerful tool in real analysis and measure theory for exchanging limits and integrals.

---

## Project Structure

The repository is organized into two main directories, one for each formalized theorem:

-   `📁 steinitz/`: Contains the formal proof of the Steinitz Exchange Lemma and an accompanying report.
-   `📁 LDCT/`: Contains the formal proof of the Lebesgue Dominated Convergence Theorem and its report.

Each directory includes the `.lean` source file, the `.tex` file for the report, and the final compiled `.pdf`.

---

## Formalized Theorems

### 1. Steinitz Exchange Lemma

The Steinitz Exchange Lemma is a fundamental result concerning the properties of spanning sets in a vector space. Informally, it states that if we have a spanning set `X` and a vector `u` that is in the span of `X` but not in the span of `X` without some vector `v`, we can "exchange" `v` for `u` without changing the span.

> **Theorem:** Let $V$ be a vector space over a field $K$. Let $X \subseteq V$. Suppose $u \in \text{span}(X)$ but $u \notin \text{span}(X \setminus \{v\})$ for some $v \in X$. If we define $Y = (X \setminus \{v\}) \cup \{u\}$, then $\text{span}(X) = \text{span}(Y)$.

-   **`steinitz/steinitz.lean`**: Contains the complete formal proof of the lemma in LEAN 4.
-   **`steinitz/steinitz.pdf`**: A detailed report discussing the formalization strategy, the challenges encountered, and a reflection on the process. It also includes an attempted formalization of a related replacement theorem.

### 2. Lebesgue Dominated Convergence Theorem (LDCT)

The LDCT provides a crucial condition under which pointwise convergence of a sequence of functions implies the convergence of their integrals. It is one of the most powerful results in measure theory.

> **Theorem:** Let $(X, \mathcal{A}, \mu)$ be a measure space. Let $g$ be an integrable function. If $\{f_n\}$ is a sequence of measurable functions such that $|f_n| \le g$ for all $n$ and $f_n \to f$ almost everywhere, then $f$ is integrable and $\lim_{n\to\infty} \int f_n \,d\mu = \int f \,d\mu$.

-   **`LDCT/LDCT.lean`**: Contains the formal proof of the theorem for extended real-valued functions. The proof relies heavily on Fatou's Lemma and navigating the properties of the `EReal` number type in LEAN.
-   **`LDCT/LDCT.pdf`**: A report detailing the formalization process, including the API developed for `EReal` and the specific challenges of working with different number types (`ℝ`, `ENNReal`, `EReal`).

---

## How to View This Project

This project does not contain programs to be compiled and run in the traditional sense. Instead, the primary artifacts are the proofs themselves and the reports analyzing them.

-   **To understand the project and the formalization process**: Start by reading the **PDF reports** in each directory (`steinitz.pdf`, `LDCT.pdf`). They provide context, explain the informal mathematics, and walk through the formal proof strategy.
-   **To inspect the formal proofs**: The `.lean` files contain the source code. They can be viewed in any text editor, but for the best experience (including interactive error checking and type inspection), they should be opened in **Visual Studio Code** with the [**LEAN 4 extension**](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) installed.
