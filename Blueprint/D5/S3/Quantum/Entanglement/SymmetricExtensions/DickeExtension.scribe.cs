using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class DickeExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Star and complete graph Bose symmetric fully PPT extensions of unnormalized Dicke diagonal operators.",
        H("Dicke diagonal extension cones"),
        Blocks(
            Paragraph(Text("The register set I and local alphabet L are finite; r is the cardinality of I. A computational basis index "
                + "is a function from I to L, so matrices act on the actual tensor product of the local "
                + "complex spaces. Two selected registers a and b are distinct and ordered. "
                + "Every partial trace below is unnormalized.")),
            Node("edgeSplit", "Splitting the actual tensor factors",
                Seq(Call("edgeSplit", X("a"), X("b")), Colon, Sp, Open, X("I"), To, X("L"), Close,
                    Sp, Equiv, Sp, Open, X("L"), Times, X("L"), Close, Times,
                    Open, Call("Rest", X("a"), X("b")), To, X("L"), Close),
                "Rest(a,b) is the subtype of registers different from both a and b. "
                + "The equivalence sends x to ((x(a),x(b)), x restricted to Rest(a,b)). "
                + "Its inverse fills a and b with the ordered pair and all other sites with the complement function. "
                + "This is a bijection of the standard tensor basis, with no change of local basis.",
                DescribeRole.Definition, false),
            Node("edgeMarginal", "The unnormalized two-register marginal",
                Seq(Sub(Call("M", X("a"), X("b"), X("E")), X("u"), X("v")), Eq,
                    new Formula.Subscript(Sum, X("c")),
                    Sub(X("E"), Call("fill", X("u"), X("c")), Call("fill", X("v"), X("c")))),
                "M(a,b,E) is partialTraceRight of E reindexed by the inverse factor split. "
                + "The sum is over every computational basis label of the complement, including its single empty "
                + "label when there are exactly two registers. There is no dimension factor.",
                DescribeRole.Definition, false),
            Node("dickeVector", "The two-particle Dicke vectors",
                Seq(Sub(X("D"), X("i"), X("i")), Eq, Tensor(Sub(X("e"), X("i")), Sub(X("e"), X("i"))),
                Sp, Comma, Sp,
                    Sub(X("D"), X("i"), X("j")), Eq,
                    new Formula.Fraction(
                        Seq(Tensor(Sub(X("e"), X("i")), Sub(X("e"), X("j"))), Plus,
                            Tensor(Sub(X("e"), X("j")), Sub(X("e"), X("i")))),
                        Seq(Sqrt, Grp(D(2)))), Sp, Open, X("i"), Neq, X("j"), Close),
                "Local labels are Fin(n), corresponding to the usual labels one through n. "
                + "The diagonal vector has one unit entry. For distinct labels the only two entries "
                + "are the positive real coefficient one over the square root of two.",
                DescribeRole.Definition, true),
            Node("dickeOperator", "The full unnormalized Dicke cone",
                Seq(Rho, Eq, new Formula.Subscript(Sum, Seq(X("i"), Leq, X("j"))),
                    Sub(X("Y"), X("i"), X("j")), Sp,
                    Sub(X("D"), X("i"), X("j")),
                    new Formula.Power(Sub(X("D"), X("i"), X("j")), Star)),
                "The coefficients are arbitrary real numbers at the definition level. "
                + "The equivalence theorem restricts every upper-triangular coefficient to be nonnegative. "
                + "Each summand is its coefficient times the outer product of the actual Dicke vector "
                + "and its complex conjugate. No coefficient sum or trace is fixed; all coefficients may vanish.",
                DescribeRole.Definition, true),
            Node("FullyPPT", "Every proper nonempty PPT cut",
                Seq(Call("FullyPPT", X("E")), Iff, Forall, Sp, X("S"), Subseteq, X("I"), Comma, Sp,
                    Seq(Emptyset, Neq, X("S"), Neq, X("I")), Implies,
                    Call("PSD", new Formula.Power(X("E"), Sub(X("T"), X("S"))))),
                "S ranges over all subsets of the register set. The condition applies to each nonempty "
                + "proper S. At the matrix-entry level partialTransposeOn exchanges the row and column "
                + "labels exactly at the sites of S, in the standard tensor basis.",
                DescribeRole.Definition, true),
            Node("leafProjector", "The symmetric leaf projector",
                Seq(Call("leafProjector", X("root")), Eq, Sub(X("P"), X("L")), Eq,
                    Tensor(X("I"), Sub(Pi, Seq(X("r"), Minus, D(1))))),
                "The distinguished root is fixed. The projector is the uniform permutation average "
                + "over the setwise stabilizer of its singleton. Such permutations fix the root and permute "
                + "all remaining registers. This is the identity on the root factor times the orthogonal "
                + "projector onto the symmetric tensor power of the leaves.",
                DescribeRole.Definition, true),
            Node("StarExtension", "The star extension predicate",
                WitnessFormula(false),
                "E is positive semidefinite on all r registers, is fixed by the genuine leaf-projector "
                + "sandwich, and has marginal rho on each ordered edge from the root to a distinct leaf. "
                + "Every proper nonempty partial transpose of this same E is positive semidefinite.",
                DescribeRole.Definition, true),
            Node("CompleteExtension", "The complete graph extension predicate",
                WitnessFormula(true),
                "E is positive semidefinite on the same r registers and is fixed by the full Bose-projector "
                + "sandwich. Its marginal is rho on every ordered pair of distinct registers. "
                + "All proper nonempty PPT cuts use this same E in the original standard basis.",
                DescribeRole.Definition, true),
            Node("result", "Equality of the extension cones",
                Seq(Forall, Sp, X("n"), Geq, D(1), Comma, Sp, Forall, Sp, X("r"), Geq, D(2), Comma, Sp,
                    Forall, Sp, X("Y"), Comma, Sp,
                    Open, Forall, Sp, X("i"), Comma, X("j"), Comma, Sp,
                    X("i"), Leq, X("j"), Implies, Sub(X("Y"), X("i"), X("j")), Geq, D(0), Close, Implies, Sp, Open,
                    Open, Exists, Sp, X("E"), Comma, Sp, Call("StarExtension", D(0), Rho, X("E")), Close,
                    Iff,
                    Open, Exists, Sp, X("E"), Comma, Sp, Call("CompleteExtension", Rho, X("E")), Close, Close),
                "Here n and r are natural numbers, Y is an arbitrary real n by n array, and i and j range "
                + "over Fin(n). The operator rho is the Dicke sum above. This is an equivalence of existence predicates "
                + "for every register count at least two and every local dimension at least one. "
                + "In the forward direction the complete graph witness is literally the star witness. "
                + "The antisymmetric two-particle projector annihilates each Dicke vector. "
                + "Trace duality lifts its zero marginal weight to zero weight of the actual tensor-placed "
                + "projector on E. The zero_weight_support_face theorem gives both one-sided annihilations "
                + "without requiring an inverse or trace normalization. Thus every root transposition fixes "
                + "every column of E. Star transpositions generate all permutations, so the columns lie in "
                + "the full symmetric subspace. The orthogonal projector and Hermiticity give the full "
                + "sandwich, and relabeling actual complement indices makes all ordered edge marginals equal. "
                + "Every PPT inequality is retained verbatim. Conversely the full symmetric subspace is "
                + "contained in the root-times-symmetric-leaves subspace, and complete edges include all "
                + "star edges. The argument includes zero coefficients, singular witnesses, n=1 and r=2. "
                + "The resolution target is exactly Gulati-Nechita-Park, arXiv:2509.15201v4, Question 8.20; "
                + "current journal question wording and worldwide absence of a prior solution are unverified.",
                DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gnp-2025-v4-question-8-20-dicke-extensions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("dicke-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Seq(params Formula[] items)
    {
        var spaced = new System.Collections.Generic.List<Formula>();
        foreach (var item in items)
        {
            if (spaced.Count != 0) spaced.Add(Sp);
            spaced.Add(item);
        }
        return F.Seq(spaced.ToArray());
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula Sub(Formula value, params Formula[] indices) =>
        new Formula.Subscript(value, Seq(indices));
    private static Formula Tensor(Formula a, Formula b) => Call("tensor", a, b);
    private static Formula WitnessFormula(bool complete)
    {
        var p = complete ? Sub(Pi, X("r")) : Sub(X("P"), X("L"));
        var marginals = complete
            ? Seq(Forall, Sp, X("a"), Comma, X("b"), Comma, Sp,
                X("a"), Neq, X("b"), Implies, Call("M", X("a"), X("b"), X("E")), Eq, Rho)
            : Seq(Forall, Sp, X("i"), Comma, Sp, X("i"), Neq, X("root"), Implies, Sp,
                Call("M", X("root"), X("i"), X("E")), Eq, Rho);
        var predicate = complete
            ? Call("CompleteExtension", Rho, X("E"))
            : Call("StarExtension", X("root"), Rho, X("E"));
        return Seq(predicate, Iff,
            Call("PSD", X("E")), Land, p, X("E"), p, Eq, X("E"), Land,
            Open, marginals, Close, Land, Call("FullyPPT", X("E")));
    }
}
