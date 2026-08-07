from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from refine_blueprint_with_lean import _node_tex_blocks  # noqa: E402
from validate_blueprint import Node  # noqa: E402


class NodeTexBlockTests(unittest.TestCase):
    def extract(self, tex: str, *, kind: str = "definition") -> str:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "content.tex"
            path.write_text(tex, encoding="utf-8")
            node = Node(label="def:target", kind=kind, file=path, line=1)
            return _node_tex_blocks({node.label: node})[node.label]

    def test_nested_matrix_does_not_truncate_node_or_following_proof(self) -> None:
        tex = r"""
\begin{definition}
  \label{def:target}
  \[
    I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\qquad
    H=\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
  \]
  The second matrix is part of the public contract.
\end{definition}
\begin{proof}
  The proof may contain \begin{aligned}a&=b\end{aligned} too.
\end{proof}
"""

        block = self.extract(tex)

        self.assertIn("H=", block)
        self.assertIn("The second matrix is part", block)
        self.assertIn(r"\begin{proof}", block)
        self.assertTrue(block.endswith(r"\end{proof}"))

    def test_balances_nested_environment_with_same_name(self) -> None:
        tex = r"""
\begin{definition}
  \label{def:target}
  \begin{definition}nested\end{definition}
  This remains in the outer node.
\end{definition}
"""

        block = self.extract(tex)

        self.assertIn("This remains in the outer node.", block)
        self.assertEqual(block.count(r"\end{definition}"), 2)

    def test_ignores_environment_tokens_inside_comments(self) -> None:
        tex = r"""
% \begin{definition}\label{def:target}wrong\end{definition}
\begin{definition}
  \label{def:target}
  % \end{definition}
  The real contract.
\end{definition}
"""

        block = self.extract(tex)

        self.assertIn("The real contract.", block)
        self.assertNotIn("wrong", block)


if __name__ == "__main__":
    unittest.main()
