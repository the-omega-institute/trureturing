using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class MeasurableFiniteMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Convexity/MeasurableFiniteMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/bayerteichmann2006tchakaloff");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integrable finite-dimensional barycenter is in the actual convex hull, and admits exact finite point evaluations.",
        H("Exact finite measurable moments"), Blocks(
            Paragraph(Text("E is any finite-dimensional real normed space; alpha is any measurable space. No compactness, closedness of the range, or continuity of the moment map is assumed. Integral is the Bochner integral. The proof descends in dimension using a supporting functional and its almost-everywhere zero kernel. This is a formalization of the cited finite-moment argument, not a claim of a new cubature theorem.")),
            Node("integral_mem_convexHull", Context(Imp(Call("IsProbabilityMeasure", Id("mu")),
                Imp(Call("Integrable", Id("f"), Id("mu")),
                Call("Mem", Integral(), Call("convexHull", Real(), Call("range", Id("f"))))))),
                "Translate the barycenter to zero. A proper span reduces dimension immediately. In full span, the affine span is full and the convex hull has nonempty interior. If zero were absent, a nonzero supporting functional would have one sign and zero integral. It vanishes almost everywhere; repair the null set by an actual point on the kernel and descend to that proper subspace."),
            Node("finite_moments_probability", Moments(true),
                "Every label is an actual point in an arbitrarily prescribed conull set. Repair its complement by one point in that set, apply actual-hull membership, and extract a finite convex combination. The weights are nonnegative and sum to one."),
            Node("finite_moments", Moments(false),
                "Normalize a nonzero finite measure to probability and rescale the weights by its total mass. For the zero measure the empty alphabet gives the exact zero moment. No numerical cardinality bound is asserted by this interface.")
        )));

    private static Formula Moments(bool probability)
    {
        var condition = Call(probability ? "IsProbabilityMeasure" : "IsFiniteMeasure", Id("mu"));
        var good = Call("AE", Id("mu"), Lambda("x", Call("Mem", Id("x"), Id("s"))));
        var witness = Exists("k", Call("Nat"), Exists("w", Arrow(Call("Fin", Id("k")), Real()),
            Exists("a", Arrow(Call("Fin", Id("k")), Id("alpha")),
                And(All("i", Call("Fin", Id("k")), Le(D(0), At(Id("w"), Id("i")))),
                And(Eq(Call("Sum", Id("w")), probability ? D(1) : Call("MeasureReal", Id("mu"), Call("univ"))),
                And(All("i", Call("Fin", Id("k")), Call("Mem", At(Id("a"), Id("i")), Id("s"))),
                    Eq(Call("Sum", Lambda("i", Call("SMul", At(Id("w"), Id("i")),
                        At(Id("f"), At(Id("a"), Id("i")))))), Integral())))))));
        return Context(All("s", Call("Set", Id("alpha")),
            Imp(condition, Imp(Call("Integrable", Id("f"), Id("mu")), Imp(good, witness)))));
    }
    private static Formula Context(Formula body) =>
        All("E", Call("Type"), All("alpha", Call("Type"),
            Seq(OpenBracket, Call("NormedAddCommGroup", Id("E")), CloseBracket, Sp,
                OpenBracket, Call("NormedSpace", Real(), Id("E")), CloseBracket, Sp,
                OpenBracket, Call("FiniteDimensional", Real(), Id("E")), CloseBracket, Sp,
                OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
                All("mu", Call("Measure", Id("alpha")), All("f", Arrow(Id("alpha"), Id("E")), body)))));
    private static Formula Integral() => Call("Integral", Id("f"), Id("mu"));
    private static DocumentBlock Node(string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("measurablefinitemoments-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        Seq(FormulaDsl.Exists, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
}
