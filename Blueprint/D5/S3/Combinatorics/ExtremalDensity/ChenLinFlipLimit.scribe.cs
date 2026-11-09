using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class ChenLinFlipLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/chenlin2026directionflips");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite tournament path defects and convergence",
        H("Finite tournament path defects and convergence"), Blocks(
            Paragraph(Text(
                "An orientation is a list of signs, with true denoting a forward arc and false a "
                + "backward arc. Its flips count adjacent unequal signs. ArcPreserving quantifies "
                + "over every map from Fin(length+1) to Fin(N); maps need not be injective. "
                + "The density homDensity is homCount divided by N^(length+1). TAS quantifies over "
                + "every positive N and every loopless tournament relation on Fin(N), with bound "
                + "(1/2)^length. Enumeration of the vertices identifies these hosts with arbitrary "
                + "finite nonempty loopless tournaments. The function f is the maximum of precisely "
                + "those m in {0,...,k} for which every length-k orientation with fewer than m flips "
                + "is TAS. The set contains zero. No property at length zero is used. "
                + "The motivating question is Question 6.1 in Hao Chen and Yupeng Lin, "
                + "Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko, "
                + "https://arxiv.org/abs/2609.14655v1.")),
            Node("flips-below-threshold", "tas_of_flips_lt", "Every word below the maximum is TAS",
                All("k", Nat, All("w", Words, Imp(Eq(Call("length", V("w")), V("k")),
                    Imp(Lt(Call("flips", V("w")), Call("f", V("k"))), Call("TAS", V("w")))))),
                "The maximum is a member of the finite set defining thresholds, with the strict "
                + "inequality on the number of flips.", DescribeRole.Theorem),
            Node("defect-upper-threshold", "f_le_flips_of_not_tas", "Every defect bounds the maximum",
                All("w", Words, Imp(Not(Call("TAS", V("w"))),
                    Le(Call("f", Call("length", V("w"))), Call("flips", V("w"))))),
                "If the maximum exceeded the flip count, the preceding threshold property would "
                + "make this word TAS, contradicting the defect.", DescribeRole.Theorem),
            Node("append-transfer", "transfer_append", "Concatenation multiplies transfers",
                MatrixFamily(All("A", Mat, All("u", Words, All("v", Words,
                    Eq(Call("transfer", V("A"), Call("append", V("u"), V("v"))),
                        Mul(Call("transfer", V("A"), V("u")), Call("transfer", V("A"), V("v")))))))),
                "This is the ordered product law for concatenated lists.", DescribeRole.Theorem),
            Node("reverse-transfer", "transfer_reflect", "Reflected words transpose transfers",
                MatrixFamily(All("A", Mat, All("w", Words,
                    Eq(Call("transfer", V("A"), Call("reflect", V("w"))),
                        Call("transpose", Call("transfer", V("A"), V("w"))))))),
                "Reversing the factors and complementing every sign transposes the ordered product.",
                DescribeRole.Theorem),
            Node("extension-sum", "extension_mass_sum", "The two extension masses have a fixed sum",
                FiniteFamily(All("A", Mat, All("M", Mat, All("d", Real,
                    Imp(All("i", V("V"), Eq(Call("rowsum", AddMatrix(V("A"), Call("transpose", V("A"))), V("i")), V("d"))),
                        Eq(Add(Call("mass", Mul(V("M"), V("A"))),
                            Call("mass", Mul(V("M"), Call("transpose", V("A"))))),
                            Mul(V("d"), Call("mass", V("M")))))))))),
                "Rowsum(A+A^T,i) denotes sum over j of A(i,j)+A(j,i). Expand matrix multiplication, "
                + "interchange the finite sums, and use this row identity.", DescribeRole.Theorem),
            Node("one-edge-padding", "exists_one_edge_padding", "One of two signs retains the average",
                FiniteFamily(All("A", Mat, All("M", Mat, All("c", Real,
                    Imp(Eq(Add(Call("mass", Mul(V("M"), V("A"))),
                            Call("mass", Mul(V("M"), Call("transpose", V("A"))))),
                        Mul(Mul(N(2), V("c")), Call("mass", V("M")))),
                        Some("b", V("Bool"), Le(Mul(V("c"), Call("mass", V("M"))),
                            Call("mass", Mul(V("M"), Call("step", V("A"), V("b"))))))))))),
                "If both signs gave strictly less than c times the old mass, their sum would be "
                + "strictly less than twice that quantity.", DescribeRole.Theorem),
            Node("recursive-padding", "exists_padding", "One-edge retention iterates to any tail length",
                MatrixFamily(All("A", Mat, All("c", Real, Imp(Le(N(0), V("c")),
                    Imp(All("u", Words, Some("b", V("Bool"),
                        Le(Mul(V("c"), MassOf(V("A"), V("u"))),
                            MassOf(V("A"), Call("append", V("u"), Call("singleton", V("b"))))))),
                        All("w", Words, All("s", Nat, Some("v", Words,
                            And(Eq(Call("length", V("v")), V("s")),
                                Le(Mul(Pow(V("c"), V("s")), MassOf(V("A"), V("w"))),
                                    MassOf(V("A"), Call("append", V("w"), V("v"))))))))))))),
                "Choose the next sign using the stated one-edge hypothesis. Induction multiplies "
                + "the lower bound by the nonnegative c at each step.", DescribeRole.Theorem),
            Node("complement-matrix", "normalizedArcMatrix_complement", "Off-diagonal tournament complements",
                MatrixFamily(All("R", Relation, Imp(Call("IsTournament", V("R")),
                    All("i", V("V"), All("j", V("V"),
                        Eq(Add(ArcEntry(V("i"), V("j")), ArcEntry(V("j"), V("i"))),
                            Call("if", Eq(V("i"), V("j")), N(0), Div(N(2), Call("card", V("V"))))))))),
                "On the diagonal both arcs are absent. Off the diagonal exactly one direction "
                + "is present and contributes 2/card(V).", DescribeRole.Theorem),
            Node("row-sum", "normalizedArcMatrix_row_sum", "The tournament extension row sum",
                FiniteFamily(Seq(Instance("Nonempty", V("V")), All("R", Relation,
                    Imp(Call("IsTournament", V("R")), All("i", V("V"),
                        Eq(Call("rowsum", AddMatrix(Call("normalizedArcMatrix", V("R")),
                                Call("transpose", Call("normalizedArcMatrix", V("R")))), V("i")),
                            Mul(N(2), PaddingFactor)))))))),
                "There are card(V)-1 off-diagonal entries, each equal to 2/card(V). "
                + "The diagonal contributes zero.", DescribeRole.Theorem),
            Node("logconvex-growth", "logconvex_geometric_lower", "Log-convexity gives geometric growth",
                All("a", Arrow(Nat, Real), Imp(Eq(Call("a", N(0)), N(1)),
                    Imp(Lt(N(0), Call("a", N(1))),
                        Imp(All("n", Nat, Le(Pow(Call("a", Add(V("n"), N(1))), N(2)),
                            Mul(Call("a", V("n")), Call("a", Add(V("n"), N(2)))))),
                            All("n", Nat, Le(Pow(Call("a", N(1)), V("n")), Call("a", V("n")))))))),
                "Induct jointly on positivity and a(1)a(n)≤a(n+1). Log-convexity and the preceding "
                + "positive term permit cancellation and give the next inequality. A second induction "
                + "gives a(1)^n≤a(n), including n=0.", DescribeRole.Theorem),
            Node("mass-powers", "mass_power_geometric", "Positive semidefinite mass dominates its first power",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("C", Mat,
                    Imp(Call("PosSemidef", V("C")), Imp(Lt(N(0), Call("mass", V("C"))),
                        All("n", Nat, Le(Pow(Call("mass", V("C")), V("n")),
                            Call("mass", Pow(V("C"), V("n")))))))))),
                "Specialize moment_geometric_lower to the all-ones vector. Its norm squared is "
                + "the positive number card(V), and its moments are exactly the matrix-power masses.",
                DescribeRole.Theorem),
            Node("abstract-spectrum-convergence", "convergence_of_defect_propagation", "The defect-spectrum criterion",
                All("F", Arrow(Nat, Nat), All("Bad", Arrow(Nat, Arrow(Nat, V("Prop"))),
                    Imp(All("k", Nat, Le(Call("F", V("k")), V("k"))),
                        Imp(All("k", Nat, Imp(Lt(N(0), V("k")),
                            Imp(Lt(Call("F", V("k")), V("k")), Call("Bad", V("k"), Call("F", V("k")))))),
                            Imp(Propagation(), ConvergenceTo("F", Call("defectLimit", V("Bad")))))))),
                "Propagation is the displayed all-large-length bound, for every positive k, every "
                + "Bad(k,r), and every positive delta: eventually F(n)/n<(r+1)/k+delta at positive n. "
                + "The defect spectrum consists of 1 and every such (r+1)/k, and defectLimit is its "
                + "infimum. The upper bound follows by choosing a spectrum element close to the "
                + "infimum. The lower bound uses saturation or Bad(n,F(n)), yielding a loss at most "
                + "1/n. Combining the two bounds gives the exact epsilon/K conclusion.",
                DescribeRole.Theorem),
            Node("density-transfer", "mass_transfer_eq_density", "The transfer counts all homomorphisms",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("R", Relation, All("w", Words,
                    Eq(TransferMass(V("w")), Mul(Pow(N(2), Call("length", V("w"))),
                        Call("homDensity", V("R"), V("w")))))))),
                "For a fixed initial vertex, expand the product by the next vertex and induct on the "
                + "word. The finite-function cons equivalence partitions all vertex assignments by "
                + "their first value. Every arc-preserving assignment contributes (2/N)^length; "
                + "every other assignment contributes zero. Summing the initial vertex and dividing "
                + "by N gives exactly 2^length times homDensity. Colliding assignments remain in the sum.",
                DescribeRole.Theorem),
            Node("defect-propagation", "defect_propagation", "Finite defects reach every large length",
                All("w", Words, Imp(Lt(N(0), Call("length", V("w"))), Imp(Not(Call("TAS", V("w"))),
                    All("d", Real, Imp(Lt(N(0), V("d")), Some("K", Nat, All("n", Nat,
                        Imp(Le(V("K"), V("n")), Imp(Lt(N(0), V("n")),
                            Lt(Div(Call("f", V("n")), V("n")),
                                Add(Div(Add(Call("flips", V("w")), N(1)),
                                    Call("length", V("w"))), V("d"))))))))))),
                "A failing TAS inequality supplies an actual finite tournament and q>1. Its order "
                + "exceeds one, since a one-vertex loopless host has zero transfer for every positive "
                + "word. Write n=2km+s. Reflection, repetition, and a selected s-edge tail give mass "
                + "at least c^(2k)(q^2)^m, which eventually exceeds one. The flip count is at most "
                + "2m(r+1)+s. Thus f(n)/n is at most (r+1)/k+2k/n. Geometric divergence and "
                + "1/n tending to zero give the displayed bound at every sufficiently large n.",
                DescribeRole.Theorem),
            Node("full-convergence-proof", "fullConvergence", "The exact threshold converges",
                V("FullConvergence"),
                "Apply the defect-spectrum criterion to F=f and to the actual predicate that a "
                + "length-k word with r flips is not TAS. The least-defect theorem discharges the "
                + "nonsaturated case; finite-defect propagation discharges the upper bound. All "
                + "hypotheses are proved for the independently defined maximum f. No numerical "
                + "value of the limit is asserted.", DescribeRole.Theorem),
            Node("sign-vectors", "signVectors", "All placements of integer signs are represented",
                All("k", Nat, Call("Equiv", Call("WordsOfLength", V("k")),
                    Arrow(Call("Fin", V("k")), V("Sign")))),
                "WordsOfLength(k) is the subtype of lists with length k. Sign is the subtype of "
                + "integers equal to -1 or 1. The equivalence is the finite-vector/list equivalence "
                + "followed pointwise by false ↔ -1 and true ↔ 1. Both inverse laws are proved. "
                + "No sign placement is excluded.", DescribeRole.Definition),
            Node("source-flips", "sourceFlips", "The source counts internal sign changes",
                All("k", Nat, All("x", Arrow(Call("Fin", V("k")), V("Sign")),
                    Eq(Call("sourceFlips", V("x")), Call("card", Call("internalflips", V("x")))))),
                "Internalflips(x) consists of indices i<k with i+1<k and x(i)x(i+1)=-1. "
                + "The definition sums its zero-or-one indicators over Fin(k). The proved "
                + "sourceFlips_eq identifies this count with the recursive list flip count under "
                + "signVectors, including lengths zero and one.", DescribeRole.Definition),
            Node("source-density", "sourceDensity", "The source density on arbitrary finite hosts",
                FiniteFamily(All("k", Nat, All("R", Relation,
                    All("x", Arrow(Call("Fin", V("k")), V("Sign")),
                        Eq(Call("sourceDensity", V("R"), V("x")),
                            Div(Call("card", Call("SourceHom", V("R"), V("x"))),
                                Pow(Call("card", V("V")), Add(V("k"), N(1))))))))),
                "SourceHom(R,x) is the subtype of all functions Fin(k+1) → V satisfying "
                + "SourceArcPreserving: sign +1 requires the forward arc and sign -1 the reverse "
                + "arc at each edge. SourceDensity_eq proves equality with homDensity after sign "
                + "encoding. HomDensity_reindex constructs an inverse-preserving bijection of these "
                + "function subtypes along any equivalence of host types and preserves the denominator.",
                DescribeRole.Definition),
            Node("arbitrary-host", "tas_arbitrary_host", "Enumeration preserves the host quantifier",
                FiniteFamily(Seq(Instance("Nonempty", V("V")), All("w", Words,
                    Imp(Call("TAS", V("w")), All("R", Relation, Imp(Call("IsTournament", V("R")),
                        Le(Call("homDensity", V("R"), V("w")),
                            Pow(Div(N(1), N(2)), Call("length", V("w")))))))))),
                "Enumerate V by Fin(card V). Pulling back the relation preserves looplessness and "
                + "the unique direction on every distinct pair. The all-function bijection proves "
                + "the density identity. Conversely, Fin(N) is one of the arbitrary finite hosts, "
                + "so SourceTAS and TAS are equivalent under signVectors.", DescribeRole.Theorem),
            Node("source-maximum", "sourceF", "The independently defined source maximum",
                All("k", Nat, Eq(Call("sourceF", V("k")), Call("max", Call("sourceThresholds", V("k"))))),
                "SourceThresholds(k) consists of precisely the m in {0,...,k} such that every "
                + "integer sign vector x with sourceFlips(x)<m is SourceTAS. SourceTAS quantifies "
                + "over all finite nonempty host types and all loopless tournament relations. "
                + "Zero belongs to this finite set, so its maximum is defined. The threshold is "
                + "strict, and the value k is retained when all orientations are TAS.",
                DescribeRole.Definition),
            Node("source-maximum-equality", "sourceF_eq_f", "The two exact maxima agree",
                All("k", Nat, Eq(Call("sourceF", V("k")), Call("f", V("k")))),
                "The sign-vector equivalence preserves flips and every arc-preserving map. "
                + "Host reindexing preserves every finite-host inequality. Hence the two finite "
                + "sets of admissible thresholds agree, and so do their maxima at every length.",
                DescribeRole.Theorem),
            Node("source-full-convergence-definition", "SourceFullConvergence", "The source limit assertion",
                Iff(V("SourceFullConvergence"), Convergence("sourceF")),
                "The epsilon/K limit is taken over all positive lengths. The same independently "
                + "defined source maximum occurs at every term. Its value at zero is outside the "
                + "quantifiers.", DescribeRole.Definition),
            Node("source-full-convergence-proof", "source_fullConvergence", "Answer to Question 6.1",
                V("SourceFullConvergence"),
                "Substitute sourceF_eq_f into fullConvergence. This proves the entire existence "
                + "of a limit for the source maximum, for arbitrary sign placements and every "
                + "finite nonempty loopless tournament. The argument proves no prescribed limit "
                + "value and uses neither a bounded host size nor a subsequence restriction.",
                DescribeRole.Theorem),
            Node("full-convergence", "FullConvergence", "Convergence over all positive lengths",
                Iff(V("FullConvergence"), Some("L", Real,
                    All("e", Real, Imp(Lt(N(0), V("e")), Some("K", Nat,
                        And(Le(N(1), V("K")), All("k", Nat, Imp(Le(V("K"), V("k")),
                            Lt(Call("abs", Sub(Div(Call("f", V("k")), V("k")), V("L"))),
                                V("e")))))))))),
                "This is the epsilon/K assertion for the source's exact strict threshold. "
                + "The positive-length quantifiers retain saturation at f(k)=k.", DescribeRole.Definition),
            Node("threshold-bounded", "f_le", "The saturated threshold is bounded",
                All("k", Nat, Le(Call("f", V("k")), V("k"))),
                "Every member of thresholds(k) belongs to {0,...,k}.", DescribeRole.Theorem),
            Node("least-defect", "exists_bad_at_f", "A nonsaturated threshold is attained by a defect",
                All("k", Nat, Imp(Lt(Call("f", V("k")), V("k")),
                    Some("w", Words, And(Eq(Call("length", V("w")), V("k")),
                        And(Eq(Call("flips", V("w")), Call("f", V("k"))),
                            Not(Call("TAS", V("w")))))))),
                "The property holds below f(k). Its failure at f(k)+1 supplies an orientation "
                + "with exactly f(k) flips, rather than merely an orientation below a different threshold.",
                DescribeRole.Theorem),
            Node("reflected-transfer", "reflected_pair_transfer", "Reflection produces a Gram transfer",
                MatrixFamily(All("A", Mat, All("w", Words,
                    Eq(Call("transfer", V("A"), Call("append", V("w"), Call("reflect", V("w")))),
                        Mul(Call("transfer", V("A"), V("w")),
                            Call("transpose", Call("transfer", V("A"), V("w")))))))),
                "Reflection reverses the word and complements every sign. It therefore transposes "
                + "the product, retaining its endpoints and their correlations.", DescribeRole.Theorem),
            Node("reflection-mass", "reflected_mass_sq_le", "Reflection amplifies the average",
                FiniteFamily(Seq(Instance("Nonempty", V("V")), All("B", Mat,
                    Le(Pow(Call("mass", V("B")), N(2)),
                        Call("mass", Mul(V("B"), Call("transpose", V("B")))))))),
                "Mass is the sum of all entries divided by the number of indices. The mass of "
                + "B times its transpose is the mean of the squares of the column sums. "
                + "Cauchy-Schwarz bounds it below by the square of the original mass. "
                + "No independent gluing of endpoint densities is used.", DescribeRole.Theorem),
            Node("tournament-padding", "tournament_padding", "Every bounded remainder admits padding",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("R", Relation,
                    Imp(Call("IsTournament", V("R")), All("w", Words, All("s", Nat,
                        Some("v", Words, And(Eq(Call("length", V("v")), V("s")),
                            Le(Mul(Pow(PaddingFactor, V("s")), TransferMass(V("w"))),
                                TransferMass(Call("append", V("w"), V("v")))))))))))),
                "Put A(i,j)=2/N when i points to j and zero otherwise. Looplessness and the unique "
                + "orientation of distinct pairs give sum_j(A(i,j)+A(j,i))=2(N-1)/N. Thus the masses "
                + "of the two possible one-edge extensions sum to 2(N-1)/N times the previous mass. "
                + "At least one sign retains a factor (N-1)/N. Induction selects an s-edge tail "
                + "retaining its s-th power, inside the same original tournament. It does not assert "
                + "that an arbitrary prescribed tail is safe.", DescribeRole.Theorem),
            Node("moment-growth", "moment_geometric_lower", "All repetition counts amplify",
                MatrixFamily(All("C", Mat, Imp(Call("PosSemidef", V("C")),
                    All("x", Arrow(V("V"), Real), Imp(Lt(N(0), Call("dot", V("x"), V("x"))),
                        Imp(Lt(N(0), Call("moment", V("C"), V("x"), N(1))), All("n", Nat,
                            Le(Pow(Call("moment", V("C"), V("x"), N(1)), V("n")),
                                Call("moment", V("C"), V("x"), V("n")))))))))),
                "Moment(C,x,n) is x dot C^n x divided by x dot x. Cauchy-Schwarz in the "
                + "positive semidefinite form C^n gives a(n+1)^2 <= a(n)a(n+2). With a(0)=1 and "
                + "a(1)>0, successive moment ratios are nondecreasing, so a(n)>=a(1)^n. "
                + "This bound holds for every natural repetition count, not only a subsequence.",
                DescribeRole.Theorem),
            Node("reflected-powers", "reflected_power_amplification", "Exponential reflected amplification",
                MatrixFamily(Seq(Instance("Nonempty", V("V")), All("B", Mat,
                    Imp(Lt(N(1), Call("mass", V("B"))), All("m", Nat,
                        Le(Pow(Call("mass", V("B")), Mul(N(2), V("m"))),
                            Call("mass", Pow(Mul(V("B"), Call("transpose", V("B"))), V("m"))))))))),
                "The all-ones moment is the mass of the matrix power. The Gram matrix is positive "
                + "semidefinite, its first mass is at least mass(B)^2, and the geometric moment "
                + "bound gives mass((B B^T)^m)>=mass(B)^(2m) for every m.", DescribeRole.Theorem),
            Paragraph(Text(
                "For the convergence argument, call (k,r) a defect when a length-k orientation "
                + "with r flips has normalized density q=2^k t(P,T)>1 in some finite host T. "
                + "For a positive-length defect N>=2. The transfer B for P has mass q. The reflected "
                + "word W=P reflect(P) has transfer C=B B^T, length 2k, and 2r+1 flips. With x "
                + "the all-ones vector, moment(C,x,m)=mass(C^m). The reflection and moment bounds "
                + "give mass(C^m)>=q^(2m).")),
            Paragraph(Text(
                "For every n write n=2km+s with 0<=s<2k. The word W repeated m times has "
                + "2m(r+1)-1 flips when m>=1. Append the tail selected by the padding inequality. "
                + "Its normalized density is at least c^s q^(2m), where c=(N-1)/N lies in (0,1). "
                + "This is at least c^(2k-1) q^(2m), which exceeds one for all sufficiently large m. "
                + "The resulting length-n path is therefore a defect for every sufficiently large n. "
                + "Its flips are at most 2m(r+1)-1+s, hence at most ((r+1)/k)n+2k. This proves "
                + "eventual upper propagation f(n)/n < (r+1)/k+delta for every positive delta.")),
            Paragraph(Text(
                "Let L be the infimum of {1} together with all (r+1)/k from defects. This nonempty "
                + "set is bounded below by zero. At a saturated length f(n)=n, one has f(n)/n>=L. "
                + "At a nonsaturated length the least-defect fact gives a defect with r=f(n), so "
                + "L<=(f(n)+1)/n. Thus f(n)/n>=L-1/n at every positive length. For the upper bound, "
                + "choose an element of the defining set below L+epsilon/2. If it is 1, saturation "
                + "bounds every f(n)/n by 1. Otherwise it is a defect ratio, and upper propagation "
                + "with delta=epsilon/2 applies to every sufficiently large length. Combining this "
                + "with 1/n<epsilon proves convergence to L over all positive lengths. The argument "
                + "does not determine a numerical value of L.")))));

    private static DocumentBlock.Describe Node(string id, string name, string title, Formula formula,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role);

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula N(int n) => new Formula.Number(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Words => Call("List", V("Bool"));
    private static Formula Mat => Call("Matrix", V("V"), V("V"), Real);
    private static Formula Relation => Arrow(V("V"), Arrow(V("V"), V("Prop")));
    private static Formula PaddingFactor => Div(Sub(Call("card", V("V")), N(1)), Call("card", V("V")));
    private static Formula TransferMass(Formula word) => Call("mass", Call("transfer",
        Call("normalizedArcMatrix", V("R")), word));
    private static Formula MassOf(Formula matrix, Formula word) => Call("mass", Call("transfer", matrix, word));
    private static Formula ArcEntry(Formula i, Formula j) => Call("entry", Call("normalizedArcMatrix", V("R")), i, j);
    private static Formula AddMatrix(Formula a, Formula b) => Add(a, b);
    private static Formula Propagation() => All("k", Nat, All("r", Nat,
        Imp(Lt(N(0), V("k")), Imp(Call("Bad", V("k"), V("r")), All("d", Real,
            Imp(Lt(N(0), V("d")), Some("K", Nat, All("n", Nat,
                Imp(Le(V("K"), V("n")), Imp(Lt(N(0), V("n")),
                    Lt(Div(Call("F", V("n")), V("n")),
                        Add(Div(Add(V("r"), N(1)), V("k")), V("d"))))))))))));
    private static Formula ConvergenceTo(string name, Formula limit) => All("e", Real,
        Imp(Lt(N(0), V("e")), Some("K", Nat, And(Le(N(1), V("K")), All("n", Nat,
            Imp(Le(V("K"), V("n")), Lt(Call("abs", Sub(Div(Call(name, V("n")), V("n")), limit)), V("e"))))))));
    private static Formula Convergence(string name) => Some("L", Real,
        All("e", Real, Imp(Lt(N(0), V("e")), Some("K", Nat,
            And(Le(N(1), V("K")), All("k", Nat, Imp(Le(V("K"), V("k")),
                Lt(Call("abs", Sub(Div(Call(name, V("k")), V("k")), V("L"))), V("e")))))))));
    private static Formula FiniteFamily(Formula body) => All("V", V("Type"),
        Seq(Instance("Fintype", V("V")), body));
    private static Formula MatrixFamily(Formula body) => All("V", V("Type"),
        Seq(Instance("Fintype", V("V")), Instance("DecidableEq", V("V")), body));
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, a);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
