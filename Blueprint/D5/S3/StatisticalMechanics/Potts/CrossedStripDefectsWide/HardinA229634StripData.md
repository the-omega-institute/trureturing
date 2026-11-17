# Width-five two-defect transfer

## Abstract

Exact-budget HDA extension.

**Definition 1.1 (Residual-budget invariant).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right) = ((d \le 2) \land (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 2 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The row and natural residual budget satisfy d at most two and horizontal defects at most two minus d; subtraction is truncated natural subtraction.

**Definition 1.2 (Class map).**

$$\forall p: \operatorname{\mathit{Fin}}\left(5\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{cl}}\left(p, d\right): \operatorname{\mathit{Fin}}\left(33\right)) = (\operatorname{\mathit{if}} (0<d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(13, \operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right)) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \operatorname{\mathit{then}} (20 + \operatorname{\mathit{Nat}}.\operatorname{\mathit{mod}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{cl}}\left(p, 0\right)\right), 6\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{let}} (code: \operatorname{\mathit{Nat}}) = (\operatorname{\mathit{if}} (\operatorname{p}\left(0\right) = \operatorname{p}\left(1\right)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(0\right) = \operatorname{p}\left(2\right)) \operatorname{\mathit{then}} (2) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(0\right) = \operatorname{p}\left(3\right)) \operatorname{\mathit{then}} (4) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(0\right) = \operatorname{p}\left(4\right)) \operatorname{\mathit{then}} (8) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(1\right) = \operatorname{p}\left(2\right)) \operatorname{\mathit{then}} (16) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(1\right) = \operatorname{p}\left(3\right)) \operatorname{\mathit{then}} (32) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(1\right) = \operatorname{p}\left(4\right)) \operatorname{\mathit{then}} (64) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(2\right) = \operatorname{p}\left(3\right)) \operatorname{\mathit{then}} (128) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(2\right) = \operatorname{p}\left(4\right)) \operatorname{\mathit{then}} (256) \operatorname{\mathit{else}} (0)) + (\operatorname{\mathit{if}} (\operatorname{p}\left(3\right) = \operatorname{p}\left(4\right)) \operatorname{\mathit{then}} (512) \operatorname{\mathit{else}} (0)) \operatorname{\mathit{in}} (\operatorname{\mathit{if}} (code \in \{201, 129, 198, 540, 340, 20, 176, 528, 192\}) \operatorname{\mathit{then}} (26) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (code \in \{513\}) \operatorname{\mathit{then}} (27) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (code \in \{37, 608\}) \operatorname{\mathit{then}} (28) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (code \in \{621, 184\}) \operatorname{\mathit{then}} (29) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (code \in \{293, 610\}) \operatorname{\mathit{then}} (30) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} (code \in \{347, 19, 73, 910, 134, 24, 336, 524, 136, 896\}) \operatorname{\mathit{then}} (31) \operatorname{\mathit{else}} (32))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The function retains HardinA229531StripData.cl at positive residual budget, subtracts one from the budget and embeds Fin 20 into Fin 33. At zero residual it appends thirteen classes: six proper classes followed by seven classes of identical zero-cost successor counts. The equality code sums powers of two for the ten equal-position predicates. Membership in each finite code set selects a class. Nat.mod denotes the nonnegative remainder modulo six. HardinA229634StripClasses.transition_counts pins every class against actual rows.

**Definition 1.3 (Block extension).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Int}}\right)) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{reindex}}\left((\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Fin}}\left(20\right) \operatorname{\mathit{Sum}} \operatorname{\mathit{Fin}}\left(13\right) \equiv \operatorname{\mathit{Fin}}\left(33\right)), (\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Fin}}\left(20\right) \operatorname{\mathit{Sum}} \operatorname{\mathit{Fin}}\left(13\right) \equiv \operatorname{\mathit{Fin}}\left(33\right)), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{fromBlocks}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{0}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{1}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{2}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{3}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{4}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{5}, B_{6}\right)\right)\right)\right)\right)\right), (0: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Fin}}\left(20\right), \operatorname{\mathit{Int}}\right)), \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{7}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{8}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{9}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{10}, B_{11}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The 33 by 33 integer matrix is reindexed from a 20 plus 13 block matrix. Its upper left block is exactly HardinA229531StripData.T and its lower left block is zero. The six proper rows of the new lower right block use the frozen terminal proper block at indices six through eleven. All appended entries are pinned by HardinA229634StripClasses.transition_counts.

Each displayed B subscript names only a row block of this presentation, with zero-based row and column indices. The Fin.append expressions concatenate these blocks in order along their first index. Every block is displayed in full below.

$$
(B_{0}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}0&0&2&2&0&2&4&0&6&2&4&4&2\\0&2&1&3&2&0&4&0&4&0&6&8&3\\2&2&0&0&1&0&4&1&2&0&4&10&2\end{pmatrix}
$$

$$
(B_{1}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}1&3&0&4&1&2&6&0&2&0&3&7&4\\0&4&1&2&2&4&8&0&2&0&2&6&2\\2&0&0&4&4&0&0&0&4&0&4&12&4\end{pmatrix}
$$

$$
(B_{2}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}0&2&0&2&2&0&0&0&0&0&2&6&2\\1&0&2&3&1&0&0&0&0&0&0&3&1\\0&4&0&2&0&4&0&0&2&0&2&0&2\end{pmatrix}
$$

$$
(B_{3}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}1&3&1&0&0&2&0&0&1&0&1&0&0\\2&2&0&0&0&0&0&0&0&0&0&0&0\\0&0&4&4&0&0&0&0&0&0&0&0&0\end{pmatrix}
$$

$$
(B_{4}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}2&6&2&3&1&2&0&0&0&0&2&3&1\\3&4&1&2&1&2&0&0&0&0&0&3&1\\0&2&2&2&1&2&0&0&1&0&1&0&0\end{pmatrix}
$$

$$
(B_{5}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}1&3&1&4&1&2&0&0&1&0&1&0&2\\1&3&1&3&2&0&2&0&0&0&0&0&0\\0&2&1&3&1&2&0&0&1&0&1&1&0\end{pmatrix}
$$

$$
(B_{6}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}1&1&1&3&2&0&2&0&0&0&0&0&0\\0&2&2&2&1&2&0&0&1&0&1&0&0\end{pmatrix}
$$

$$
(B_{7}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(6, 6\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(6, 7\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(6, 8\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(6, 9\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(6, 10\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(6, 11\right)&0&0&0&0&0&0&0\\\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(7, 6\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(7, 7\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(7, 8\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(7, 9\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(7, 10\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(7, 11\right)&0&0&0&0&0&0&0\\\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(8, 6\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(8, 7\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(8, 8\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(8, 9\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(8, 10\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(8, 11\right)&0&0&0&0&0&0&0\end{pmatrix}
$$

$$
(B_{8}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(9, 6\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(9, 7\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(9, 8\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(9, 9\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(9, 10\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(9, 11\right)&0&0&0&0&0&0&0\\\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(10, 6\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(10, 7\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(10, 8\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(10, 9\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(10, 10\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(10, 11\right)&0&0&0&0&0&0&0\\\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(11, 6\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(11, 7\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(11, 8\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(11, 9\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(11, 10\right)&\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}\left(11, 11\right)&0&0&0&0&0&0&0\end{pmatrix}
$$

$$
(B_{9}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}0&0&0&0&0&0&0&0&0&0&0&0&0\\0&0&1&0&0&0&0&0&0&0&0&0&0\\0&0&1&1&0&0&0&0&0&0&0&0&0\end{pmatrix}
$$

$$
(B_{10}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}1&0&0&0&0&0&0&0&0&0&0&0&0\\1&0&1&1&0&0&0&0&0&0&0&0&0\\1&1&0&0&0&0&0&0&0&0&0&0&0\end{pmatrix}
$$

$$
(B_{11}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(1\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}1&1&1&0&0&0&0&0&0&0&0&0&0\end{pmatrix}
$$

**Definition 1.4 (Initial distribution).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(33\right) \to \operatorname{\mathit{Int}}) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{initial}}, \begin{pmatrix}0&0&0&0&0&0&30&6&0&12&0&24&0\end{pmatrix}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

Fin.append retains HardinA229531StripData.initial and appends thirteen weights counting initial rows with two horizontal defects. The literal initial-row sum is checked in HardinA229634Strip.finite_certificate.

**Definition 1.5 (Terminal indicator).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{\mathit{terminal}}: \operatorname{\mathit{Fin}}\left(33\right) \to \operatorname{\mathit{Int}}) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((0: \operatorname{\mathit{Fin}}\left(20\right) \to \operatorname{\mathit{Int}}), (1: \operatorname{\mathit{Fin}}\left(13\right) \to \operatorname{\mathit{Int}})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The first twenty entries are zero and the appended thirteen entries are one. The finite certificate identifies this with zero residual budget for every valid row.

**Definition 1.6 (Forward vectors).**

$$(\operatorname{\mathit{HardinA229634StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(21\right) \to \left(\operatorname{\mathit{Fin}}\left(33\right) \to \operatorname{\mathit{Int}}\right)) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((\Lambda (i: \operatorname{\mathit{Fin}}\left(14\right)) \mapsto (\operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{W}\left(i\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{0}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{1}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{2}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{3}, B_{4}\right)\right)\right)\right)\left(i\right)\right))), \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{5}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(B_{6}, B_{7}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229634: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229634>.

*Commentary.*

The 21 by 33 integer table keeps all fourteen available forward rows from HardinA229531StripData.W in the inherited block. The remaining entries are explicit integers. HardinA229634Strip.finite_certificate pins row zero to initial, all twenty matrix steps, and the order-eighteen relation at row twenty.

Each displayed B subscript names only a row block of this presentation, with zero-based row and column indices. The Fin.append expressions concatenate these blocks in order along their first index. Every block is displayed in full below.

$$
(B_{0}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}0&0&0&0&0&0&30&6&0&12&0&24&0\\168&396&168&396&198&204&264&6&204&12&264&456&192\\4104&6624&3444&5208&1860&2868&1632&54&1848&156&2376&4212&1800\end{pmatrix}
$$

$$
(B_{1}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}60864&97284&49896&69732&22704&42204&14232&480&18900&1500&24600&44208&19116\\818808&1305552&649698&880896&276018&563340&130536&4350&189900&14196&253584&470340&204732\\10372524&16511124&8022828&10662660&3242910&7105212&1218408&40338&1894308&134028&2591400&4952892&2165664\end{pmatrix}
$$

$$
(B_{2}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}126058428&200385168&95508810&125053632&37132386&86092020&11451816&378012&18793692&1265460&26288088&51655344&22644888\\1485603204&2359034184&1106387568&1431733920&416763834&1012629876&107936880&3558474&185784528&11949180&265184088&534131244&234528492\\17096480808&27126769416&12547062444&16082614596&4603376772&11639936196&1018492872&33560754&1831765188&112836108&2663101080&5482472364&2409867708\end{pmatrix}
$$

$$
(B_{3}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}193050744984&306140334600&139886100720&177885607020&50182685244&131357287476&9614928816&316759884&18023190336&1065532596&26644003248&55917809856&24598879008\\2146342936788&3402355705224&1537914190518&1942534928964&541071639030&1460123024292&90785254080&2990632266&177024763536&10062107604&265708300512&567210973020&249682094928\\23556308766720&37331339165544&16711271711664&20985421966716&5779628845914&16025809276332&857269733472&28239071766&1736062861584&95019476052&2642227523904&5726243056476&2521995967020\end{pmatrix}
$$

$$
(B_{4}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}255711859899972&405174631394352&179792385938598&224630570251404&61243171981482&174005292412164&8095301613552&266661283176&17001558309528&897298407876&26207504428776&57568042110024&25366203281100\\2749789907518668&4356566464503588&1917863490177024&2385404263597320&644440881446898&1871801495581980&76445865341256&2518132037430&166284863868684&8473472087748&259345880188512&576623106792108&254179646800656\end{pmatrix}
$$

$$
(B_{5}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}377816268254310&600743597088780&224555831893872&257919522373656&57143078782662&262936173555204&3964410013601988&6273118331236404&2629397804913408&3169373717402208&801222692975520&2699592780852384&154888939419840&74871249978372&143633364808332&191192141414088&0&143633364808332&0&143633364808332&29328363557493828&46462937115413520&20306200339283316&25155431593951704&6739782271472796&19972309696866684&721900210654944&23779388302878&1624418866577160&80017689441468&2561076732432936&5756774027016276&2538533556212352\\3567839532212298&5673015341754576&2120550398541462&2435612999697780&539618433050190&2482992077796588&40016752044499248&63340646654601612&26363434120229256&31690406664204384&7956370348888536&27288304623704352&1462663722670020&707031186161400&1356376133597400&1805487797385144&0&1356376133597400&0&1356376133597400&310563243312713604&491991684109600068&213596596127856048&263653513699563108&70105198388616720&211587308140867284&6817124553451080&224555831893872&15851115121270284&755632536508620&25242598871144280&57305030388964320&25277562373337052\\33692247232519926&53572101603834552&20025026636010066&23000258068758036&5095781831289432&23447693903526924&402250578723172668&636878660917845252&263436590697761388&315892062117033480&78818905539501348&274644834239171832&13812392861205300&6676713796780704&12808694406179172&17049795203262096&0&12808694406179172&0&12808694406179172&3267713645334471324&5176680713716897872&2233758865680892650&2748285051878414256&725687169325679874&2227373021945726148&64376246552621544&2120550398541462&154514521636897548&7135679064424596&248360418587101344&568931804468937060&251031172550509428\end{pmatrix}
$$

$$
(B_{6}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(3\right), \operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}318166644053060898&505898482300303776&189102689240942004&217198729140989472&48121066536057534&221424085479762804&4028616164614284792&6380014356333047964&2624438106168031128&3140105669893440360&779104154423170620&2753648770441935840&130434805805818020&63050311340778168&120956596068874404&161006649340894536&0&120956596068874404&0&120956596068874404&34187569220817562248&54160557724327858452&23239300485687694140&28507769595593646276&7479227717518086750&23314763357106588084&607925304952321848&20025026636010066&1504715920431036396&67384494465039852&2439651883683199752&5634960361904931660&2486975920924505904\\3004549175342189334&4777360954955383392&1785756944565356586&2051076740242403592&454422484917989010&2090978423666254956&40215807217489068684&63702557850899068044&26074516524362429748&31135958119085466300&7685879700891067680&27515366798024284152&1231737395728995276&595404107622873480&1142231770406425572&1520437148888309580&0&1142231770406425572&0&1142231770406425572&355856300861898385272&563771030532517504608&240647455056032299890&294406296196514459184&76780942897028863962&242801682490883581548&5740832169511623816&189102689240942004&14639993425051630092&636333288106121796&23928963150009194952&55690239860178034608&24584588818770106368\\28372916912642961462&45114144845228427492&16863472419930867834&19368971645091260436&4291256169725749188&19745777107927655364&400284414638994582816&634181252413076589420&258422334151636967424&308030631277253263464&75682813649978725788&274112644991571075288&11631688980057495432&5622590629373116764&10786459305639762060&14357973194770475232&0&10786459305639762060&0&10786459305639762060&3687040607169827061768&5841485303653601070792&2481442327248533863032&3028253403590875775040&785407454658131808306&2516905499803979646444&54212508620250050880&1785756944565356586&142315288533909099864&6009098350684378668&234378591948944732664&549296640099958857084&242540981865882407052\end{pmatrix}
$$

$$
(B_{7}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(1\right), \operatorname{\mathit{Fin}}\left(33\right), \operatorname{\mathit{Int}}\right)) = \begin{pmatrix}267934511129194046202&426027271948149173376&159247151325193095708&182907379140010105332&40523700234747877458&186465677731598088636&3973731007228324719324&6296795049646520623764&2555500817493031503456&3041074241090777843124&743995757749383307092&2723348457057190487256&109841750310238919028&53095916484952996104&101859978670514350416&135586923510376086084&0&101859978670514350416&0&101859978670514350416&38041920903512156924028&60273717355540152964968&25489303839255020336124&31035081736087946411652&8007851252436368678124&25981205483652482142396&511946015939562583272&16863472419930867834&1382317240450194814836&56745833825285922924&2292727820038422899496&5408118757647961990476&2388421696545671355204\end{pmatrix}
$$

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData](../CrossedStripDefects/HardinA229531StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
