using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSParentIntersectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rank-four target locus is inhabited at every length at least four, and raw three-site marginals recover every actual periodic competitor up to phase on that locus.",
        H("Periodic MPS parent-space gluing"),
        Blocks(
            Definition("wordMatrix", "Ordered matrix words",
                "A word of length n is a function from Fin n to Fin 2. wordMatrix multiplies the shared complex two by two matrices in increasing site order; the empty product is the identity."),
            Definition("gamma", "Virtual boundary amplitudes",
                "For a complex two by two matrix X, gamma A n X at the word w is the trace of X times wordMatrix A w. Its image is the length-n parent space."),
            Definition("TwoSiteSpanning", "Length-two injectivity",
                "TwoSiteSpanning means that the complex linear span of all four ordered products A(i)A(j) is the full two by two matrix space. Neither individual symbol matrix is required to be invertible."),
            Definition("twoFlattening", "The actual target flattening",
                "For r natural, the target has length r+4. A row is the ordered pair of its first two bits, and a column is a word of length r+2. The entry is the existing native traceWord amplitude at the concatenation of these words. Thus rank four is the intrinsic amplitude-flattening condition of Definition 1.3."),
            Definition("competitorSlice", "Actual conditional four-site amplitudes",
                "For arbitrary complex shared matrices B and a fixed complement word b of length r, competitorSlice is the native periodic traceWord amplitude at the concatenation of a four-bit word with b. The ring has length 4+r. At r=0 the complement word is empty."),
            Definition("threeColumns", "Three-site amplitude columns",
                "For a ring of length r+4, rows are words w of length three and columns are complement words b of length r+1. The entry is trace(wordMatrix A b times wordMatrix A w). Trace cyclicity identifies this entry with the actual native traceWord amplitude at the concatenation of w and b."),
            Definition("rawThree", "Raw three-site marginal",
                "rawThree A r is threeColumns A r times its conjugate transpose. Its entry at u,v is the sum over complement words b of the actual amplitude at ub times the complex conjugate of the amplitude at vb. This is the unnormalized marginal of Definition 1.2; no division by the state norm occurs."),
            Describe.Lean(
                DescribeId.Create("periodic-mps-actual-competitor-gluing"),
                DeclarationHandle.Create(Module + ".actual_competitor_gluing"),
                H("Gluing adjacent three-site constraints"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The matrices A and B are arbitrary complex shared two by two matrices. Only the target flattening for A has rank four. No injectivity, rank or nondegeneracy condition is imposed on B; repeated and zero competitor matrices remain in the domain.")),
                    Paragraph(Text("Assume the two adjacent three-site conditional vectors of the fixed four-site slice lie in the target three-site parent space. The left condition supplies one boundary X(j) for each last bit; the right condition supplies one boundary Y(i) for each first bit. The conclusion supplies a single matrix Z representing the entire four-site slice.")),
                    Paragraph(Text("Rank four forces the two-letter target products to span the matrix algebra. Trace separation on the two middle sites then gives X(j)A(i)=A(j)Y(i). Expanding the identity in the two-letter products constructs a common boundary with X(j)=A(j)Z and Y(i)=ZA(i). Cyclicity of the trace gives the asserted four-site representation.")),
                    Paragraph(Text("This is the adjacent-parent overlap bridge in Section 2 of Periodic binary matrix product states: three-site phase recovery. It includes the four-site ring without identifying the range of its three-site marginal with the full three-site parent space. Equality of raw marginals, all-window propagation, finite-ring scalar uniqueness, the unit-modulus conclusion and genericity require their separate arguments; none is asserted by this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-mps-rank-locus-phase-recovery"),
                DeclarationHandle.Create(Module + ".rank_locus_inhabited_and_phase_recovery"),
                H("Inhabited rank locus and finite-ring phase recovery"),
                StatementSource.FromAuthor(RecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural r the ring length is r+4. The first conjunct exhibits a shared matrix pair whose actual two-site flattening has rank four. The second quantifies over every target pair A and every competitor pair B, imposing rank four only on A. It states both directions of equality of raw three-site marginals versus equality of the actual periodic amplitude functions up to a complex scalar of norm one. gamma A n 1 is definitionally the existing traceWord amplitude function.")),
                    Paragraph(Text("The witness uses the diagonal matrix with entries 1 and 2 and the matrix exchanging the two coordinates. Their four length-two products span the full matrix algebra. Trace separation at every longer length gives rank four for every r, including zero.")),
                    Paragraph(Text("Equality of raw marginals identifies the ranges of the two amplitude-column matrices, because a complex matrix and its product with its conjugate transpose have the same range. Every competitor three-site slice therefore lies in the target parent space. The adjacent-parent intersection propagates these constraints by induction to one virtual boundary for the whole ring. Both induction branches compare coefficients of the same actual competitor using trace cyclicity.")),
                    Paragraph(Text("The competitor's cyclic invariance forces the resulting boundary to commute with both target symbol matrices. Length-two spanning then makes it commute with every two by two matrix, hence it is scalar. The nonzero raw target marginal and its scalar multiplication law force the scalar to have norm one. At r=0 the propagation reaches the four-site ring with an empty complement; no equality between the marginal range and the entire three-site parent space is required.")),
                    Paragraph(Text("This establishes the inhabited-locus and actual-competitor phase-equivalence clauses of Section 2, Theorem 2.1. Relative Zariski openness and density, ordinary density, the observable determinant and partial-trace criterion, and Corollary 3.1 are separate obligations. They are not conclusions of this declaration."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-mps-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula TheoremFormula()
    {
        Formula a = X("A"), b = X("B"), r = X("r"), tail = X("b");
        Formula left = Exists("X", Arrow(Bit(), Bond()),
            All("w", Word(D(3)), All("j", Bit(), Eq(
                At(Local("competitorSlice"), b, tail, At(Q("Fin", "snoc"), X("w"), X("j"))),
                At(Local("gamma"), a, D(3), At(X("X"), X("j")), X("w"))))));
        Formula right = Exists("Y", Arrow(Bit(), Bond()),
            All("i", Bit(), All("w", Word(D(3)), Eq(
                At(Local("competitorSlice"), b, tail, At(Q("Fin", "cons"), X("i"), X("w"))),
                At(Local("gamma"), a, D(3), At(X("Y"), X("i")), X("w"))))));
        Formula conclusion = Exists("Z", Bond(), Eq(
            At(Local("competitorSlice"), b, tail), At(Local("gamma"), a, D(4), X("Z"))));
        Formula rank = Eq(At(Q("Matrix", "rank"), At(Local("twoFlattening"), a, r)), D(4));
        return Disp(All("A", Arrow(Bit(), Bond()), All("B", Arrow(Bit(), Bond()),
            All("r", Naturals(), Imp(rank, All("b", Word(r), Imp(left, Imp(right, conclusion))))))));
    }

    private static Formula RecoveryFormula()
    {
        Formula r = X("r"), a = X("A"), b = X("B"), c = X("c");
        Formula rank = Eq(At(Q("Matrix", "rank"), At(Local("twoFlattening"), a, r)), D(4));
        Formula inhabited = Exists("A", Arrow(Bit(), Bond()), rank);
        Formula raw = Eq(At(Local("rawThree"), b, r), At(Local("rawThree"), a, r));
        Formula length = new Formula.Binary(r, FormulaBinaryOperator.Add, D(4));
        Formula phase = Exists("c", Seq(Mathbb, Grp(X("C"))), And(
            Eq(At(Q("norm"), c), D(1)),
            Eq(At(Local("gamma"), b, length, D(1)),
                At(Q("HSMul", "hSMul"), c, At(Local("gamma"), a, length, D(1))))));
        Formula recovery = All("A", Arrow(Bit(), Bond()), All("B", Arrow(Bit(), Bond()),
            Imp(rank, new Formula.Logic(Par(raw), FormulaLogicOperator.Iff, Par(phase)))));
        return Disp(All("r", Naturals(), And(inhabited, recovery)));
    }

    private static Formula X(string value) => F.Id(value);
    private static Formula Q(params string[] names)
    {
        var parts = new List<Formula>();
        foreach (var name in names) { if (parts.Count > 0) parts.Add(Dot); parts.Add(X(name)); }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Local(string name) => Q("D5", "S3", "Quantum", "TensorNetworks", "PeriodicMPSParentIntersection", name);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) => Par(Seq(f, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Par(body));
    private static Formula Exists(string name, Formula type, Formula body) => Seq(F.Exists, Sp, Typed(X(name), type), Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => new Formula.TypeArrow(Par(a), Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Bit() => At(Q("Fin"), D(2));
    private static Formula Bond() => Local("Bond");
    private static Formula Word(Formula n) => At(Local("Word"), n);
}
