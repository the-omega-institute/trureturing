using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class CircularDeletionTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/CircularDeletionTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An oriented circular word with no repeated initial labels cannot reverse by deleting and reinserting labels while three initial labels remain untouched.",
        H("Circular Deletion Transport"),
        Blocks(
            Paragraph(Text(
                "An oriented circular word is a finite list modulo rotation, using the native Cycle carrier. "
                + "The quotient identifies rotations; it does not additionally identify reversal. Restriction filters a chosen set of labels before taking the rotation class. "
                + "Deleting x is restriction to labels different from x. A deletion step between C and D requires that deleting x "
                + "from both gives exactly the same oriented residual circle. DeleteWalk records a finite sequence of these steps "
                + "and its omission word xs; repeated omissions and omissions outside the initial support are allowed.")),
            Describe.Lean(DescribeId.Create("restriction-reversal"),
                DeclarationHandle.Create(Prefix + "restrict_reverse"),
                H("Restriction Commutes with Reversal"),
                StatementSource.FromAuthor(ReverseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every label type A, Boolean predicate p and oriented circle C, restricting reverse(C) "
                    + "equals reversing restrict(p,C). Choose a list representative of C. Filtering its reversal equals "
                    + "reversing its filtered list, and this equality descends to the rotation quotient. "
                    + "The label type may be infinite; the theorem requires no equality decision on A."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("restriction-composition"),
                DeclarationHandle.Create(Prefix + "restrict_restrict"),
                H("Successive Restrictions Compose"),
                StatementSource.FromAuthor(CompositionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every label type A, Boolean predicates p and q and oriented circle C, restriction by q "
                    + "followed by p is restriction by the Boolean conjunction of their values. BoolAnd in the displayed "
                    + "formula denotes Lean's Boolean conjunction, and the arrow expression denotes a function of y. "
                    + "Choose a list representative of C. Filtering it twice equals filtering once by that Boolean "
                    + "conjunction, and the equality descends to the rotation quotient."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("untouched-restriction"),
                DeclarationHandle.Create(Prefix + "restrict_walk"),
                H("Untouched Circular Restrictions Are Preserved"),
                StatementSource.FromAuthor(RestrictionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every Boolean predicate p that excludes every omitted label, restriction to p is the same at both ends "
                    + "of a deletion walk. Filtering commutes with rotation, so restriction is independent of the chosen list "
                    + "representative. If p excludes x, filtering after deleting x equals filtering directly. Applying that equality "
                    + "to each deletion step and composing along the walk proves preservation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("negative-support-bound"),
                DeclarationHandle.Create(Prefix + "negative_walk_support_bound"),
                H("Negative Transport Omits All but Two Initial Labels"),
                StatementSource.FromAuthor(SupportFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let C have no repeated labels. If a deletion walk ends at C.reverse, the number of distinct initial labels "
                    + "is at most the number of distinct omitted labels plus two. Three untouched initial labels would retain their "
                    + "circular restriction throughout the walk. That restriction has exactly three distinct labels, so its orientation "
                    + "differs from its reverse. This contradicts the negative endpoint. Counting the untouched support gives the bound. "
                    + "The ambient label type may be infinite, and intermediate circles need not have the initial support."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "If C has no repeated labels and contains all n labels, the bound gives at least n minus two distinct omissions. "
                + "Its use for a whole-supplier incidence requires an actual equality of oriented deletion residuals at that incidence. "
                + "Equality after also identifying reversal is insufficient. This result neither constructs a Hamilton cycle "
                + "nor establishes a boundary-preserving supplier lift.")))));
    private static Formula ReverseFormula()
    {
        Formula a = F.Id("A"), p = F.Id("p"), c = F.Id("C");
        Formula equality = new Formula.Relation(Call("restrict", p, Call("reverse", c)),
            FormulaRelationOperator.Equal, Call("reverse", Call("restrict", p, c)));
        return Disp(All("A", Call("Type"), All("p", Seq(a, Sp, To, Sp, Call("Bool")),
            All("C", Call("Cycle", a), equality))));
    }

    private static Formula CompositionFormula()
    {
        Formula a = F.Id("A"), p = F.Id("p"), q = F.Id("q"), c = F.Id("C"), y = F.Id("y");
        Formula meet = Seq(Open, y, Sp, Mapsto, Sp,
            Call("BoolAnd", new Formula.Apply(p, [y]), new Formula.Apply(q, [y])), Close);
        Formula equality = new Formula.Relation(Call("restrict", p, Call("restrict", q, c)),
            FormulaRelationOperator.Equal, Call("restrict", meet, c));
        Formula predicate = Seq(a, Sp, To, Sp, Call("Bool"));
        return Disp(All("A", Call("Type"), All("p", predicate, All("q", predicate,
            All("C", Call("Cycle", a), equality)))));
    }

    private static Formula RestrictionFormula()
    {
        Formula a = F.Id("A"), xs = F.Id("xs"), c = F.Id("C"), d = F.Id("D"), p = F.Id("p");
        Formula untouched = All("x", a, Implies(
            new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf, xs),
            new Formula.Relation(new Formula.Apply(p, [F.Id("x")]),
                FormulaRelationOperator.Equal, Call("false"))));
        Formula equality = new Formula.Relation(Call("restrict", p, c),
            FormulaRelationOperator.Equal, Call("restrict", p, d));
        return Disp(All("A", Call("Type"), WithEquality(a,
            All("xs", Call("List", a), All("C", Call("Cycle", a), All("D", Call("Cycle", a),
                All("p", Seq(a, Sp, To, Sp, Call("Bool")),
                    Implies(Call("DeleteWalk", xs, c, d), Implies(untouched, equality)))))))));
    }

    private static Formula SupportFormula()
    {
        Formula a = F.Id("A"), xs = F.Id("xs"), c = F.Id("C");
        Formula bound = new Formula.Relation(Call("card", Call("toFinset", c)),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Binary(Call("card", Call("toFinset", xs)), FormulaBinaryOperator.Add, D(2)));
        return Disp(All("A", Call("Type"), WithEquality(a,
            All("xs", Call("List", a), All("C", Call("Cycle", a),
                Implies(Call("DeleteWalk", xs, c, Call("reverse", c)),
                    Implies(Call("Nodup", c), bound)))))));
    }

    private static Formula WithEquality(Formula a, Formula body) =>
        Seq(OpenBracket, Call("DecidableEq", a), CloseBracket, Sp, body);

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
