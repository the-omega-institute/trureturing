using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FiniteKrausRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite rectangular completely positive matrix map has a finite Kraus witness.",
        H("Finite Kraus Representations"), Blocks(Describe.Lean(
            DescribeId.Create("finite-kraus-representation"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus"),
            H("Complete positivity gives a rectangular Kraus family"),
            StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("IsCompletelyPositive")), Open, F.Id("Phi"), Close, Sp, Rightarrow, Sp, Exists, Sp, F.Id("M"), Comma, Sp, F.Id("Phi"), Eq, Operatorname, Grp(F.Id("ofKraus")), Open, F.Id("M"), Comma, F.Id("M"), Close, Dot))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/watrous2018theory")), Blocks(
                Paragraph(Text("For finite coordinate types A and B with decidable equality and an RCLike scalar, every completely positive rectangular MatrixMap Φ has a witness family M indexed by B × A and equals the associated Kraus sum (ofKraus denotes the Lean function of_kraus). This is a CP representation statement; it does not assert trace preservation.")),
                Paragraph(Text("The declaration is the selected upstream Physlib result at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260, routed from QuantumInfo/Channels/MatrixMap.lean and Unbundled.lean. Finite and decidable assumptions are retained explicitly."))),
            DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application: three-weight Pauli Bayesian inversion"), Blocks(
                Paragraph(Text("The following application establishes the three-weight alternative in Ting, Fullwood and Wu, Operational time-reversal symmetry for unital qubit channels, arXiv:2605.10375v1, Section V (Library/QuantumStates/ting2026operational.md): a Bayesian inverse exists exactly at the maximally mixed state. The full exact Lean application and its suppliers are kernel-checked, with axiom closure limited to propext, Classical.choice and Quot.sound. The argument is exposition under this existing owner; it carries no new theorem declaration or problem-resolution status.")),
                Paragraph(Text("Let p be any nonnegative real probability vector on four labels with exactly three nonzero entries. Set sigma = (I, X, Y, Z), with Y = i X Z, and define the complex-linear Pauli channel P by the Kraus sum below. Let rho range over all complex 2 by 2 positive semidefinite matrices of trace one. A proposed reverse map F ranges over all complex-linear matrix maps, with complete positivity at every finite amplification and trace preservation on every matrix. It need not be Pauli or unital. The target is Hilbert–Schmidt self-adjointness of P and existence of such a Bayesian F exactly when rho is I/2.")),
                Display(Equal(App("P", F.Id("A")), SumAt(Mu,
                    Seq(Ix("p", Mu), Sp, Ix("sigma", Mu), F.Id("A"), Ix("sigma", Mu))))),
                Display(Equal(App("tr", Seq(Pow(F.Id("A"), Star), App("P", F.Id("B")))),
                    App("tr", Seq(Pow(Paren(App("P", F.Id("A"))), Star), F.Id("B"))))),
                Paragraph(Text("Cyclicity of trace and the Hermitian Pauli involutions give the displayed adjoint identity for every pair of matrices A and B. The operators sqrt(p_mu) sigma_mu give complete positivity through FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive. Normalization gives P(I) = I; the adjoint identity at A = I then gives trace preservation on all matrices. These are applications of the original MatrixMap and IsCPTP predicates used by CoPRelativeQuantumnessRefutation.")),
                Paragraph(Text("Write rho = (I + r dot sigma)/2. The first projection of ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian supplies this representation from Hermiticity; norm_bloch_le_trace_of_posSemidef gives sum r_i squared at most one. The module name ActualPureQubitGeometry imposes no purity premise on these facts. Here the coordinates numbered 1, 2, 3 correspond to Lean Fin 3 indices 0, 1, 2 and to X, Y, Z respectively.")),
                Display(Equal(Rho, new Formula.Fraction(Add(F.Id("I"), App("spin", F.Id("r"))), F.D(2)))),
                Display(Equal(F.Id("lambda"), Tuple(
                    Seq(Ix("p", F.D(0)), Plus, Ix("p", F.D(1)), Minus, Ix("p", F.D(2)), Minus, Ix("p", F.D(3))),
                    Seq(Ix("p", F.D(0)), Minus, Ix("p", F.D(1)), Plus, Ix("p", F.D(2)), Minus, Ix("p", F.D(3))),
                    Seq(Ix("p", F.D(0)), Minus, Ix("p", F.D(1)), Minus, Ix("p", F.D(2)), Plus, Ix("p", F.D(3)))))),
                Display(Equal(Ix("s", F.Id("i")), Multiply(Ix("lambda", F.Id("i")), Ix("r", F.Id("i"))))),
                Paragraph(Text("Entrywise Pauli multiplication gives P(rho) = (I + s dot sigma)/2. Zero individual coordinates of r are allowed, and the norm bound includes pure states.")))),
            new DocumentBlock.Section(H("Literal Bayes rule and output-first Choi coordinates"), Blocks(
                Paragraph(Text("Use the paper's unnormalized Jamiołkowski convention J[N] = sum E_ij tensor N(E_ji), with E_ij the matrix unit. The original Bayesian equation is the following anticommutator identity; the displayed trace identity justifies replacing the adjoint of P by P.")),
                Display(Equal(App("J", F.Id("N")), SumAt(F.Id("i"), SumAt(F.Id("j"),
                    App("kron", App("E", F.Id("i"), F.Id("j")), App("N", App("E", F.Id("j"), F.Id("i")))))))),
                Display(Equal(App("anti", App("kron", App("P", Rho), F.Id("I")), App("J", F.Id("F"))),
                    App("anti", App("kron", F.Id("I"), Rho), App("J", F.Id("P"))))),
                Paragraph(Text("Here anti(U,V) means UV + VU. The selected Choi definition is C_F[(b,i),(c,j)] = F(E_ij)[b,c], output index first, with no dimension-normalizing factor. The identity C_F[(b,i),(c,j)] = J[F][(j,b),(i,c)] reindexes the literal Bayes rule to the following equation. It does not assume positivity of J[F], and it does not substitute a partial transpose of C_F for C_F.")),
                Display(Equal(App("anti", App("kron", F.Id("I"), Pow(Paren(App("P", Rho)), F.Id("T"))), Ix("C", F.Id("F"))),
                    App("anti", App("kron", Rho, F.Id("I")), Ix("C", F.Id("P"))))),
                Paragraph(Text("FiniteKrausRepresentation supplies choi_matrix and choi_PSD_iff_CP_map in namespace FiniteKrausChannel.PhyslibLeaf.MatrixMap. The latter is stated CP(F) iff PSD(C_F); its forward direction supplies positivity for arbitrary F. It is the selected Physlib source at revision 6a09b2d1761a0d4430083045a247eb121d8da260. The supplier compiles with only the standard axioms propext, Classical.choice and Quot.sound; it has no frozen-state membership.")))),
            new DocumentBlock.Section(H("A denominator-free Sylvester implication"), Blocks(
                Paragraph(Text("Put C = C_F, V = I tensor transpose(spin(s)), q = sum s_i squared, and R = anti(rho tensor I, C_P). Then V squared is q I and the reindexed Bayes equation becomes C + (VC + CV)/2 = R. Associativity and distribution, using V squared = q I, give the polynomial implication below.")),
                Display(Equal(Multiply(Subtract(F.D(1), F.Id("q")), F.Id("C")),
                    Add(Subtract(Multiply(Subtract(F.D(1), new Formula.Fraction(F.Id("q"), F.D(2))), F.Id("R")),
                        new Formula.Fraction(Add(Seq(F.Id("V"), F.Id("R")), Seq(F.Id("R"), F.Id("V"))), F.D(2))),
                        new Formula.Fraction(Seq(F.Id("V"), F.Id("R"), F.Id("V")), F.D(2))))),
                Paragraph(Text("Denote the right side by T. The implication is valid also at q = 1: it then forces T = 0 whenever the Sylvester equation holds. It does not establish existence or uniqueness of C at q = 1. No division by 1 - q occurs. For the actual normalized three-weight channel and nonzero Bloch input the separate strict-contraction argument below gives q < 1.")))),
            new DocumentBlock.Section(H("All four missing weights and their witness evaluations"), Blocks(
                Paragraph(Text("Let k be the unique missing Pauli label. In each row below a lists the three active weights in X, Y, Z coordinate order. Set h_i = (1 - a_i) r_i, H = sum h_i squared, A = sum a_i h_i squared, B = sum a_i squared (1 - a_i) r_i squared, K = sum a_i squared r_i squared, and N(a,r) = (1 - H)B + KA. The witness w_k is the output-first vectorization of (I - spin(h)) sigma_k, with entry order (0,0), (0,1), (1,0), (1,1). The symbols h in each row are formed from that row's a; the imaginary unit is i.")),
                Display(Equal(App("N", F.Id("a"), F.Id("r")),
                    Add(Multiply(Subtract(F.D(1), F.Id("H")), F.Id("B")), Multiply(F.Id("K"), F.Id("A"))))),
                WitnessCase(0, Tuple(Ix("p", F.D(1)), Ix("p", F.D(2)), Ix("p", F.D(3))),
                    Tuple(Subtract(F.D(1), Ix("h", F.D(3))), Add(Negative(Ix("h", F.D(1))), Imaginary(Ix("h", F.D(2)))),
                        Subtract(Negative(Ix("h", F.D(1))), Imaginary(Ix("h", F.D(2)))), Add(F.D(1), Ix("h", F.D(3))))),
                WitnessCase(1, Tuple(Ix("p", F.D(0)), Ix("p", F.D(3)), Ix("p", F.D(2))),
                    Tuple(Add(Negative(Ix("h", F.D(1))), Imaginary(Ix("h", F.D(2)))), Subtract(F.D(1), Ix("h", F.D(3))),
                        Add(F.D(1), Ix("h", F.D(3))), Subtract(Negative(Ix("h", F.D(1))), Imaginary(Ix("h", F.D(2)))))),
                WitnessCase(2, Tuple(Ix("p", F.D(3)), Ix("p", F.D(0)), Ix("p", F.D(1))),
                    Tuple(Subtract(Negative(Imaginary(Ix("h", F.D(1)))), Ix("h", F.D(2))), Negative(Imaginary(Paren(Subtract(F.D(1), Ix("h", F.D(3)))))),
                        Imaginary(Paren(Add(F.D(1), Ix("h", F.D(3))))), Subtract(Imaginary(Ix("h", F.D(1))), Ix("h", F.D(2))))),
                WitnessCase(3, Tuple(Ix("p", F.D(2)), Ix("p", F.D(1)), Ix("p", F.D(0))),
                    Tuple(Subtract(F.D(1), Ix("h", F.D(3))), Subtract(Ix("h", F.D(1)), Imaginary(Ix("h", F.D(2)))),
                        Subtract(Negative(Ix("h", F.D(1))), Imaginary(Ix("h", F.D(2)))), Negative(Add(F.D(1), Ix("h", F.D(3)))))),
                Paragraph(Text("Each row is a literal polynomial evaluation after setting p_k to zero and imposing sum p_mu = 1. The four rows cover the entire three-weight simplex; no symmetry reduction discards a coordinate-zero or pure-state boundary. The witness norm H and output norm q are distinct polynomials and are never identified.")))),
            new DocumentBlock.Section(H("Strict sign, mixed-state converse and limits"), Blocks(
                Paragraph(Text("Normalization and exactly three nonzero nonnegative weights give 0 < a_i < 1. If r is nonzero, select a coordinate j with r_j nonzero. Termwise, (1 - a_i) squared is less than one; summing and using the strict term at j gives H < sum r_i squared <= 1. The j term of B is strictly positive and all other terms are nonnegative, so B > 0. Both A and K are nonnegative. Consequently N(a,r) > 0, including when sum r_i squared = 1 or some other coordinates vanish.")),
                Paragraph(Text("For every row the squared contraction coefficient lambda_i squared equals (2 a_i - 1) squared, which is strictly less than one. The same strict-sum argument yields q < sum r_i squared <= 1 for nonzero r. Thus T = (1 - q) C_F would be positive semidefinite if F were completely positive, while the corresponding row gives a strictly negative quadratic form. This is the obstruction for arbitrary F; no restriction to F = P enters the converse direction.")),
                Paragraph(Text("When r = 0, rho = I/2 and F = P provides the reverse channel: the Kraus argument gives CPTP, P(I/2) = I/2, and both literal Bayes anticommutators equal J[P]. This treats the maximally mixed state directly and makes no strict-sign assertion at r = 0. The forward obstruction uses positivity and trace one of the input, not invertibility of the input.")),
                Paragraph(Text("The checked application composes the stated suppliers with finite polynomial and order normalization. Its conclusion is the full original Pauli statement: the reverse map ranges over all CPTP F, whereas the paper's Theorem 1 and Proposition 2 characterize only the adjoint candidate. The exact endpoint retains every normalized three-weight vector and every PSD trace-one input. This exposition makes no worldwide novelty, completed problem-resolution, or general four-weight claim.")))))));

    private static DocumentBlock Display(Formula value) => new DocumentBlock.DisplayFormula(value);
    private static Formula App(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Ix(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula Negative(Formula value) => Seq(Minus, Paren(value));
    private static Formula Imaginary(Formula value) => Seq(F.Id("i"), Sp, value);
    private static Formula SumAt(Formula index, Formula value) => Seq(Sum, Underscore, Grp(index), Sp, value);
    private static Formula Tuple(params Formula[] values)
    {
        Formula[] items = new Formula[values.Length * 2 - 1];
        for (int index = 0; index < values.Length; index++)
        {
            items[index * 2] = values[index];
            if (index + 1 < values.Length) items[index * 2 + 1] = Comma;
        }
        return Paren(Seq(items));
    }
    private static DocumentBlock WitnessCase(byte k, Formula active, Formula entries)
    {
        Formula w = Ix("w", F.D(k));
        return Paragraph(
            Text("For missing label " + k + ": "),
            Math(Equal(Ix("p", F.D(k)), F.D(0))), Text(", "),
            Math(Equal(F.Id("a"), active)), Text(", "),
            Math(Equal(w, entries)), Text("; "),
            Math(Equal(App("Re", Seq(Pow(w, Star), F.Id("T"), w)),
                Seq(Minus, F.D(4), App("N", active, F.Id("r"))))), Text("."));
    }
}
