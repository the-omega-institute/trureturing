using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class SchurComplementAssociativityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequential and one-shot Schur elimination give the same retained operator.",
        H("Schur Complement Associativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sequential-schur-elimination-is-associative"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.schur_complement_associativity"),
                H("Sequential elimination equals one-shot elimination"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H0, H1, and H2 be complete complex inner-product spaces. "
                            + "Nine bounded maps are the blocks of an operator on their "
                            + "three-fold product.")),
                    Paragraph(Text(
                        "Suppose the H2 block, the H1 block obtained after eliminating H2, "
                            + "and the combined lower block have the displayed inverse "
                            + "witnesses. Then sequentially eliminating H2 and H1 gives "
                            + "the same retained H0 operator as eliminating H1 times H2 "
                            + "in one step.")),
                    Paragraph(Text(
                        "The proof applies the combined lower inverse to the retained "
                            + "column, solves its two block equations successively, and "
                            + "substitutes those solutions into the retained row."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Comp(Formula outer, Formula inner) =>
        Call("comp", outer, inner);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula h0 = F.Id("H0");
        Formula h1 = F.Id("H1");
        Formula h2 = F.Id("H2");
        Formula lowerSpace = Call("Prod", h1, h2);
        Formula a00 = F.Id("A00");
        Formula a01 = F.Id("A01");
        Formula a02 = F.Id("A02");
        Formula a10 = F.Id("A10");
        Formula a11 = F.Id("A11");
        Formula a12 = F.Id("A12");
        Formula a20 = F.Id("A20");
        Formula a21 = F.Id("A21");
        Formula a22 = F.Id("A22");
        Formula a22Inv = F.Id("A22Inv");
        Formula reducedA11Inv = F.Id("reducedA11Inv");
        Formula lowerInv = F.Id("lowerInv");

        Formula Map(Formula domain, Formula codomain) =>
            Call("ContinuousLinearMap", complex, domain, codomain);

        Formula reducedA11 = Subtract(a11, Comp(a12, Comp(a22Inv, a21)));
        Formula lowerBlock = Call(
            "prod",
            Call("coprod", a11, a12),
            Call("coprod", a21, a22));
        Formula assumptions = And(
            Call("NormedAddCommGroup", h0),
            And(
                Call("InnerProductSpace", complex, h0),
                And(
                    Call("CompleteSpace", h0),
                    And(
                        Call("NormedAddCommGroup", h1),
                        And(
                            Call("InnerProductSpace", complex, h1),
                            And(
                                Call("CompleteSpace", h1),
                                And(
                                    Call("NormedAddCommGroup", h2),
                                    And(
                                        Call("InnerProductSpace", complex, h2),
                                        And(
                                            Call("CompleteSpace", h2),
                                            And(
                                                Equal(
                                                    Comp(a22Inv, a22),
                                                    Call("id", complex, h2)),
                                                And(
                                                    Equal(
                                                        Comp(reducedA11Inv, reducedA11),
                                                        Call("id", complex, h1)),
                                                    Equal(
                                                        Comp(lowerBlock, lowerInv),
                                                        Call("id", complex, lowerSpace)))))))))))));

        Formula sequential = Subtract(
            Subtract(a00, Comp(a02, Comp(a22Inv, a20))),
            Comp(
                Subtract(a01, Comp(a02, Comp(a22Inv, a21))),
                Comp(
                    reducedA11Inv,
                    Subtract(a10, Comp(a12, Comp(a22Inv, a20))))));
        Formula oneShot = Subtract(
            a00,
            Comp(
                Call("coprod", a01, a02),
                Comp(lowerInv, Call("prod", a10, a20))));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("H0", type),
                Bound("H1", type),
                Bound("H2", type),
                Bound("A00", Map(h0, h0)),
                Bound("A01", Map(h1, h0)),
                Bound("A02", Map(h2, h0)),
                Bound("A10", Map(h0, h1)),
                Bound("A11", Map(h1, h1)),
                Bound("A12", Map(h2, h1)),
                Bound("A20", Map(h0, h2)),
                Bound("A21", Map(h1, h2)),
                Bound("A22", Map(h2, h2)),
                Bound("A22Inv", Map(h2, h2)),
                Bound("reducedA11Inv", Map(h1, h1)),
                Bound("lowerInv", Map(lowerSpace, lowerSpace)),
            ],
            Implies(assumptions, Equal(sequential, oneShot)));
    }
}
