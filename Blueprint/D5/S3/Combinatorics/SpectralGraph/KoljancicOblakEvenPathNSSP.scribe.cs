using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class KoljancicOblakEvenPathNSSPDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/koljancic2026nssp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-support witnesses for every positive even double path and every nonempty loop set.",
        H("Even looped paths allow the non-symmetric Strong Spectral Property"), Blocks(
            Paragraph(Text("The target is the unchanged existential event in Koljančić–Oblak Question 5.11. Both orientations of every consecutive path edge occur, and the only additional arcs are exactly the loops at the nonempty vertex set L. The source vertex i corresponds to Fin n value i minus one. Every real test matrix X is permitted. In particular, no symmetry or diagonal condition is imposed on X.")),
            Describe.Lean(DescribeId.Create("koljancic-even-path-nssp-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP.result"),
                H("The complete all-orders and all-loop-sets event"),
                StatementSource.FromAuthor(Disp(Event())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive even order and every nonempty loop set, an exact-support real matrix exists for which entrywise annihilation and the transpose commutator force every real test matrix to vanish. The constructed witnesses are symmetric, but symmetry is a choice in the existential proof and is not an extra condition on the event. Order two, endpoint loops and empty branches are included."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("koljancic-oblak-2026-question-5-11-even-loop-path"), ResolutionKind.Proved)),
            Paragraph(Text("Fix a loop vertex r and let s be the number of vertices on its other side. Then r+s is odd. The existing coprime_positive_branches relation supplies strictly positive squared edge parameters on both branches with coprime continuants. Taking their real square roots gives nonzero real edge weights, and the central loop weight is one. The literal joinedPath matrix has exactly the singleton-loop pattern.")),
            Paragraph(Text("The matrix is a real symmetric Jacobi matrix with all adjacent coefficients nonzero. The original GibbsStochasticSimpleSpectrum.jacobi_simple supplier gives a characteristic polynomial with simple complex roots; the Hermitian spectral theorem supplies a real orthogonal eigenbasis. The roots/eigenvalues correspondence makes its diagonal eigenvalue function injective. This application uses the original Jacobi proof, with its telescope unchanged.")),
            Paragraph(Text("The support tangent has r+s+1 coordinates. Its readout is the diagonal after orthogonal conjugation. If the readout vanishes, the evaluated characteristic derivative vanishes: at a diagonal matrix each determinant row-replacement summand has a zero column. Applying joined_path_charpoly_derivative, polynomial extensionality and joined_variation_injective recovers every tangent coordinate. Equal finite dimensions make the readout surjective.")),
            Paragraph(Text("For an unrestricted commuting X, orthogonal conjugation of its transpose gives a matrix commuting with a diagonal matrix with distinct entries, hence a diagonal matrix Y. Entrywise annihilation gives trace orthogonality against every support tangent. Choose a tangent whose spectral diagonal is diag(Y). The resulting trace equals the sum of squares of the diagonal entries of Y, so Y and X vanish. This proves the singleton-loop witness against the full real commutant.")),
            Paragraph(Text("For enlargement, send A to the linear map X mapped to the pair consisting of its entrywise product with A and the transpose commutator. HasNSSP is exactly injectivity of this map. In finite dimensions the family is continuous and the set of injective continuous linear maps is open. Add the same sufficiently small positive value at all remaining loops in L. The off-diagonal entries and chosen central loop retain their values, the newly required loops are nonzero, and all other diagonal entries are zero. Openness preserves nSSP. Similarity preservation from the published Superpattern Lemma is unnecessary for this existential event.")),
            Paragraph(Text("The source question and published definitions are literature inputs. The continuant construction and its synthesis with the original Jacobi supplier and openness of injectivity are repository derivations. Source and license boundaries are in Library/Eigenstructure/koljancic2026nssp.md. Bounded source qualification does not assert worldwide priority or exhaustive nonresolution.")))));

    private static Formula Event()
    {
        Formula n = V("n"), l = V("L"), a = V("A"), x = V("X");
        Formula i = V("i"), j = V("j"), fin = Call("Fin", n);
        Formula real = Seq(Operatorname, Grp(V("Real")));
        Formula matrix = Call("Matrix", fin, fin, real);
        Formula pattern = Or(Eq(Add(Call("val", i), D(1)), Call("val", j)),
            Or(Eq(Add(Call("val", j), D(1)), Call("val", i)),
                And(Eq(i, j), new Formula.Relation(i, FormulaRelationOperator.MemberOf, l))));
        Formula support = All("i", fin, All("j", fin, Iff(Ne(App(a, i, j), D(0)), pattern)));
        Formula entry = All("i", fin, All("j", fin, Eq(Mul(App(a, i, j), App(x, i, j)), D(0))));
        Formula commutator = Eq(Sub(Mul(a, Call("transpose", x)), Mul(Call("transpose", x), a)), D(0));
        Formula nssp = All("X", matrix, Imp(entry, Imp(commutator, Eq(x, D(0)))));
        Formula witness = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("A"),
            matrix, And(support, nssp));
        return All("n", Call("Nat"), Imp(Lt(D(0), n), Imp(Call("Even", n),
            All("L", Call("Finset", fin), Imp(Call("Nonempty", l), witness)))));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        a.Length == 0 ? Seq(Operatorname, Grp(V(s))) : App(Seq(Operatorname, Grp(V(s))), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
}
