using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class BinaryRenyiPowerMonotonicityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Entropy/RenyiCombining/BinaryRenyiPowerMonotonicityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/liu2026binaryentropyhardness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powered binary Renyi entropy can decrease as its positive order increases.",
        H("A decrease between orders one quarter and one half"),
        Blocks(
            Node("powered", "The powered binary entropy", PoweredFormula(),
                "Write hRenyi(alpha,x) for the binary Renyi entropy with natural logarithms: "
                    + "log(x^alpha + (1-x)^alpha)/(1-alpha). The normalization log(2) "
                    + "is the entropy of a fair bit. The outer exponent is a real power.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Monotonicity in the order", ClaimFormula(),
                "Section 1.4(b) asks whether the powered entropy is non-decreasing in alpha "
                    + "for every fixed x in [0,1]. This proposition compares any two positive "
                    + "orders a < b distinct from one; the value at order one requires a limiting definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The monotonicity proposition is false",
                new Formula.Not(Named("claim")),
                "At x = 1/17, the quarter-order entropy is "
                    + "(4/3)(log(3) - log(17)/4), while the half-order entropy is log(25/17). "
                    + "The identities 16^(1/4) = 2 and 16^(1/2) = 4 give these expressions. "
                    + "The integer inequalities 17^4 times 2^9 < 3^16 and 25^16 < 17^16 times 2^9, "
                    + "together with strict monotonicity of the logarithm, imply "
                    + "hRenyi(1/4,1/17)/log(2) > 3/4 and "
                    + "0 < hRenyi(1/2,1/17)/log(2) < 9/16. "
                    + "Raising these positive bounds to the eighth and fourth powers and using "
                    + "(3/4)^8 = (9/16)^4 gives powered(1/2,1/17) < powered(1/4,1/17). "
                    + "Both orders are positive and distinct from one, and 1/17 lies in [0,1].",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("liu-binary-renyi-power-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), RealType(), body);
    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Imp(Formula premise, Formula body) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, body);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula PoweredFormula()
    {
        Formula alpha = F.Id("alpha"), x = F.Id("x");
        return All("alpha", All("x", Rel(Call("powered", alpha, x), FormulaRelationOperator.Equal,
            new Formula.Power(
                Fraction(Call("hRenyi", alpha, x), Call("log", D(2))), Fraction(D(2), alpha)))));
    }

    private static Formula ClaimFormula()
    {
        Formula x = F.Id("x"), a = F.Id("a"), b = F.Id("b");
        Formula comparison = Rel(Call("powered", a, x), FormulaRelationOperator.LessThanOrEqual,
            Call("powered", b, x));
        Formula orders = All("a", All("b",
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, a),
            Imp(Rel(a, FormulaRelationOperator.LessThan, b),
            Imp(new Formula.Not(Rel(a, FormulaRelationOperator.Equal, D(1))),
            Imp(new Formula.Not(Rel(b, FormulaRelationOperator.Equal, D(1))), comparison))))));
        Formula proposition = All("x",
            Imp(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, x),
            Imp(Rel(x, FormulaRelationOperator.LessThanOrEqual, D(1)), orders)));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, proposition);
    }
}
