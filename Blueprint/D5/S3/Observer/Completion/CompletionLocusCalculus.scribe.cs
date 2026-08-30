using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class CompletionLocusCalculusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Completion/CompletionLocusCalculus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural completion loci compose by intersection, pull back along arbitrary parameter maps, and retain gauge stability under conjunction.",
        H("Completion Locus Calculus"),
        Blocks(
            Theorem(
                "completion-locus-pair-eq-inter",
                "completion_locus_pair_eq_inter",
                CompletionLocusPairEqInterFormula(),
                "Completion Locus Pair eq Inter",
                "Conjoining two normalizations and pairing their defects gives exactly the intersection of their completion loci.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-locus-preimage",
                "completion_locus_preimage",
                CompletionLocusPreimageFormula(),
                "Completion Locus Preimage",
                "Completion loci pull back exactly along arbitrary parameter maps.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-locus-intersection-gauge-stable",
                "completion_locus_intersection_gauge_stable",
                CompletionLocusIntersectionGaugeStableFormula(),
                "Completion Locus Intersection Gauge Stable",
                "If two completion loci are stable under the same gauge action, their conjoined locus is stable as well.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula CompletionLocusPairEqInterFormula() => Statement(
    [Typed(Seq(F.Id("A")), Seq(F.Id("Type"))), Typed(Seq(F.Id("D"), Underscore, Grp(D(1))), Seq(F.Id("Type"))), Typed(Seq(F.Id("D"), Underscore, Grp(D(2))), Seq(F.Id("Type"))), Typed(Seq(F.Id("normalization"), Underscore, Grp(D(1))), Seq(F.Id("Set"), Sp, F.Id("A"))), Typed(Seq(F.Id("normalization"), Underscore, Grp(D(2))), Seq(F.Id("Set"), Sp, F.Id("A"))), Typed(Seq(F.Id("defect"), Underscore, Grp(D(1))), new Formula.TypeArrow(Seq(F.Id("A")), Seq(F.Id("D"), Underscore, Grp(D(1))))), Typed(Seq(F.Id("defect"), Underscore, Grp(D(2))), new Formula.TypeArrow(Seq(F.Id("A")), Seq(F.Id("D"), Underscore, Grp(D(2))))), Typed(Seq(F.Id("zero"), Underscore, Grp(D(1))), Seq(F.Id("D"), Underscore, Grp(D(1)))), Typed(Seq(F.Id("zero"), Underscore, Grp(D(2))), Seq(F.Id("D"), Underscore, Grp(D(2))))],
        [],
        [],
        Seq(F.Id("completionPointSet"), Sp, Open, F.Id("normalization"), Underscore, Grp(D(1)), Sp, F.Id("intersection"), Sp, F.Id("normalization"), Underscore, Grp(D(2)), Close, Sp, Open, LambdaLower, Sp, F.Id("a"), Sp, Mapsto, Sp, Open, F.Id("defect"), Underscore, Grp(D(1)), Sp, F.Id("a"), Comma, Sp, F.Id("defect"), Underscore, Grp(D(2)), Sp, F.Id("a"), Close, Close, Sp, Open, F.Id("zero"), Underscore, Grp(D(1)), Comma, Sp, F.Id("zero"), Underscore, Grp(D(2)), Close, Sp, Eq, Sp, F.Id("completionPointSet"), Sp, F.Id("normalization"), Underscore, Grp(D(1)), Sp, F.Id("defect"), Underscore, Grp(D(1)), Sp, F.Id("zero"), Underscore, Grp(D(1)), Sp, F.Id("intersection"), Sp, F.Id("completionPointSet"), Sp, F.Id("normalization"), Underscore, Grp(D(2)), Sp, F.Id("defect"), Underscore, Grp(D(2)), Sp, F.Id("zero"), Underscore, Grp(D(2))));

private static Formula CompletionLocusPreimageFormula() => Statement(
    [Typed(Seq(F.Id("A")), Seq(F.Id("Type"))), Typed(Seq(F.Id("A"), Apos), Seq(F.Id("Type"))), Typed(Seq(F.Id("D")), Seq(F.Id("Type"))), Typed(Seq(F.Id("parameterMap")), new Formula.TypeArrow(Seq(F.Id("A"), Apos), Seq(F.Id("A")))), Typed(Seq(F.Id("normalization")), Seq(F.Id("Set"), Sp, F.Id("A"))), Typed(Seq(F.Id("defect")), new Formula.TypeArrow(Seq(F.Id("A")), Seq(F.Id("D")))), Typed(Seq(F.Id("zeroD")), Seq(F.Id("D")))],
        [],
        [],
        Seq(F.Id("completionPointSet"), Sp, Open, F.Id("parameterMap"), Sp, Caret, Grp(Minus, D(1)), Sp, F.Id("normalization"), Close, Sp, Open, F.Id("defect"), Sp, Circ, Sp, F.Id("parameterMap"), Close, Sp, F.Id("zeroD"), Sp, Eq, Sp, F.Id("parameterMap"), Sp, Caret, Grp(Minus, D(1)), Sp, Open, F.Id("completionPointSet"), Sp, F.Id("normalization"), Sp, F.Id("defect"), Sp, F.Id("zeroD"), Close));

private static Formula CompletionLocusIntersectionGaugeStableFormula() => Statement(
    [Typed(Seq(F.Id("G")), Seq(F.Id("Type"))), Typed(Seq(F.Id("A")), Seq(F.Id("Type"))), Typed(Seq(F.Id("D"), Underscore, Grp(D(1))), Seq(F.Id("Type"))), Typed(Seq(F.Id("D"), Underscore, Grp(D(2))), Seq(F.Id("Type"))), Typed(Seq(F.Id("normalization"), Underscore, Grp(D(1))), Seq(F.Id("Set"), Sp, F.Id("A"))), Typed(Seq(F.Id("normalization"), Underscore, Grp(D(2))), Seq(F.Id("Set"), Sp, F.Id("A"))), Typed(Seq(F.Id("defect"), Underscore, Grp(D(1))), new Formula.TypeArrow(Seq(F.Id("A")), Seq(F.Id("D"), Underscore, Grp(D(1))))), Typed(Seq(F.Id("defect"), Underscore, Grp(D(2))), new Formula.TypeArrow(Seq(F.Id("A")), Seq(F.Id("D"), Underscore, Grp(D(2))))), Typed(Seq(F.Id("zero"), Underscore, Grp(D(1))), Seq(F.Id("D"), Underscore, Grp(D(1)))), Typed(Seq(F.Id("zero"), Underscore, Grp(D(2))), Seq(F.Id("D"), Underscore, Grp(D(2))))],
        [Seq(OpenBracket, Call("Group", Seq(F.Id("G"))), CloseBracket), Seq(OpenBracket, Call("MulAction", Seq(F.Id("G")), Seq(F.Id("A"))), CloseBracket)],
        [Seq(Forall, Sp, Open, F.Id("g"), Sp, Colon, Sp, F.Id("G"), Close, Sp, OpenBrace, F.Id("a"), Sp, Colon, Sp, F.Id("A"), CloseBrace, Comma, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("completionPointSet"), Sp, F.Id("normalization"), Underscore, Grp(D(1)), Sp, F.Id("defect"), Underscore, Grp(D(1)), Sp, F.Id("zero"), Underscore, Grp(D(1)), Sp, Rightarrow, Sp, F.Id("g"), Sp, Cdot, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("completionPointSet"), Sp, F.Id("normalization"), Underscore, Grp(D(1)), Sp, F.Id("defect"), Underscore, Grp(D(1)), Sp, F.Id("zero"), Underscore, Grp(D(1))), Seq(Forall, Sp, Open, F.Id("g"), Sp, Colon, Sp, F.Id("G"), Close, Sp, OpenBrace, F.Id("a"), Sp, Colon, Sp, F.Id("A"), CloseBrace, Comma, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("completionPointSet"), Sp, F.Id("normalization"), Underscore, Grp(D(2)), Sp, F.Id("defect"), Underscore, Grp(D(2)), Sp, F.Id("zero"), Underscore, Grp(D(2)), Sp, Rightarrow, Sp, F.Id("g"), Sp, Cdot, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("completionPointSet"), Sp, F.Id("normalization"), Underscore, Grp(D(2)), Sp, F.Id("defect"), Underscore, Grp(D(2)), Sp, F.Id("zero"), Underscore, Grp(D(2)))],
        Seq(Forall, Sp, Open, F.Id("g"), Sp, Colon, Sp, F.Id("G"), Close, Sp, OpenBrace, F.Id("a"), Sp, Colon, Sp, F.Id("A"), CloseBrace, Comma, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("completionPointSet"), Sp, Open, F.Id("normalization"), Underscore, Grp(D(1)), Sp, F.Id("intersection"), Sp, F.Id("normalization"), Underscore, Grp(D(2)), Close, Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Mapsto, Sp, Open, F.Id("defect"), Underscore, Grp(D(1)), Sp, F.Id("value"), Comma, Sp, F.Id("defect"), Underscore, Grp(D(2)), Sp, F.Id("value"), Close, Close, Sp, Open, F.Id("zero"), Underscore, Grp(D(1)), Comma, Sp, F.Id("zero"), Underscore, Grp(D(2)), Close, Sp, Rightarrow, Sp, F.Id("g"), Sp, Cdot, Sp, F.Id("a"), Sp, InMacro, Sp, F.Id("completionPointSet"), Sp, Open, F.Id("normalization"), Underscore, Grp(D(1)), Sp, F.Id("intersection"), Sp, F.Id("normalization"), Underscore, Grp(D(2)), Close, Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Mapsto, Sp, Open, F.Id("defect"), Underscore, Grp(D(1)), Sp, F.Id("value"), Comma, Sp, F.Id("defect"), Underscore, Grp(D(2)), Sp, F.Id("value"), Close, Close, Sp, Open, F.Id("zero"), Underscore, Grp(D(1)), Comma, Sp, F.Id("zero"), Underscore, Grp(D(2)), Close));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
