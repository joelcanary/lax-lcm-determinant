# The determinant of the least-common-multiple matrix

**Lax Lean Archive record [`lax-426240`](https://laxarchive.org/lax-426240/)** — registered, permanent and citable.
Every statement in `concepts/` is proved in `proofs/` with no assumptions: **3 of 3 statements proved**,
rebuilt by the archive on its own machines against a pinned Mathlib before registration.

Smith (1875) showed that the determinant of the $N \times N$ matrix $\big(\gcd(i,j)\big)$ is $\varphi(1)\cdots\varphi(N)$, and more generally that $\det\big(f(\gcd(i,j))\big) = \prod_{k \le N} g(k)$ whenever $f(m) = \sum_{d \mid m} g(d)$. This submission evaluates the companion determinant of least common multiples. Since $\mathrm{lcm}(i,j)\gcd(i,j) = ij$, the lcm matrix factors as $D S D$ with $D = \mathrm{diag}(1,\dots,N)$ and $S_{ij} = 1/\gcd(i,j)$, and $1/m$ is the Dirichlet convolution of $g = \mu * (1/\cdot)$ with the constant function $1$ by Möbius inversion. Hence

$$\det\big(\mathrm{lcm}(i,j)\big)_{i,j \le N} = (N!)^2 \prod_{k \le N} g(k) = N!\prod_{k \le N}\prod_{p \mid k}(1 - p),$$

using $\sum_{d \mid n}\mu(d)\,d = \prod_{p \mid n}(1-p)$ for every $n \ge 1$. The three statements are the determinant in terms of $g$, the closed form $g(n) = \tfrac{1}{n}\prod_{p\mid n}(1-p)$, and the closed form of the determinant. Smith's factorisation over a commutative ring and the Möbius product identity for arbitrary $n$ appear as helpers of the proofs and are not claimed as archive content.

## What is inside

| Concept | Type | Title | Proved / stated |
|---|---|---|---|
| `LcmDeterminant` | theorem | The determinant of the least-common-multiple matrix | 3 / 3 |

Each concept file states its results as `axiom`s beside a natural-language description
(that is the archive's format: statements are separated from proofs); the proof of each
one lives in `proofs/` and is checked by the Lean kernel. `build-output.json` is the
archive's own build record for this source commit.

## How to cite

In LaTeX, cite the record id: `\cite{lax-426240}`. The archive resolves it to the exact
statements and proofs, and a registered record cannot change under the citation
(a correction would be a new record that supersedes this one).

```bibtex
@misc{lax426240,
  author = {Cruz Cabrera, Joel},
  title = {The determinant of the least-common-multiple matrix},
  year = {2026},
  howpublished = {Lax Lean Archive, record lax-426240},
  url = {https://laxarchive.org/lax-426240/}
}
```

Author: Joel Cruz Cabrera, ORCID [0009-0005-4048-1237](https://orcid.org/0009-0005-4048-1237).

## Rebuilding it

```bash
npm install -g lax-archive
lax build          # Lean v4.33.0, Mathlib db584cd6d46c
```

The pins are in `manifest.yaml`; the archive's build of this commit
(`cafe603`) is recorded in `build-output.json`
(`archiveSha` `ca12986a6e04`).

## Related

- The four records and their live counts: https://kodamaseclabs.com/publications
- Smith's determinant over any commutative ring, and the Redheffer determinant, are submitted to Mathlib separately (pull requests #43884 and #43758); this record does not duplicate them.

## Use of AI

An AI tool (an agent running on the author's machine) wrote the Lean under the
author's direction; the author set the statements, reviewed every declaration
and checked the build before submitting. The archive then rebuilt everything
independently. What is proved is exactly what the kernel accepted, no more.

## License

Apache-2.0 (the archive's required license), see `LICENSE`.

<details><summary>BibTeX entries the record itself cites</summary>

```bibtex
@article{smith1875,
  author = {Smith, Henry John Stephen},
  title = {On the value of a certain arithmetical determinant},
  journal = {Proceedings of the London Mathematical Society},
  volume = {7},
  year = {1875},
  pages = {208--212}
}
```
</details>
