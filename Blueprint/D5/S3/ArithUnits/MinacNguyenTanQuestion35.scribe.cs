using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MinacNguyenTanQuestion35Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MinacNguyenTanQuestion35.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/minacnguyentan2026sums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact n-sum property with restricted augmentation transfers from a finite field "
            + "to every finite group algebra.",
        H("Exact sums of units with prescribed augmentation"),
        Blocks(
            Node("HasNSumProperty", "Exactly n summands", SumPropertyFormula(),
                "For every element r there is a function a on Fin n, every value belongs to S, "
                    + "and the sum of all its values is r. Repetitions are allowed.",
                DescribeRole.Definition),
            Node("augmentation", "The standard coefficient-sum augmentation", AugmentationFormula(),
                "The algebra homomorphism is MonoidAlgebra.lift of the constant-one group "
                    + "homomorphism. Its value on a group-algebra element is the sum of its "
                    + "coefficients over the finite support; for a finite group this is also "
                    + "the sum over all group elements.", DescribeRole.Definition),
            Node("augmentationUnitSubgroup", "Units with augmentation in U", UnitSubgroupFormula(),
                "This is the preimage of U under Units.map of the standard augmentation. "
                    + "All summands are genuine units of the actual MonoidAlgebra.",
                DescribeRole.Definition),
            Node("result", "Question 3.5 has an affirmative answer", ResultFormula(),
                "The finite field has more than two elements, U contains minus one, n is at "
                    + "least two, and the field has the exact n-sum property with respect to U. "
                    + "The conclusion uses the same n for every element of the actual finite "
                    + "group algebra. It includes modular characteristic, arbitrary "
                    + "noncommutative finite groups, characteristic two fields with more than "
                    + "two elements, and the trivial group. The Jacobson quotient is decomposed "
                    + "into finite matrix algebras. Orthogonal idempotents select the factor "
                    + "seen by augmentation; its injective map to F identifies its entries "
                    + "with scalars. The given field sums control that factor. Rank normal "
                    + "form and a scalar distinct from zero and one construct two units in "
                    + "every other factor; extra units give n summands. Quotient units lift "
                    + "through the nilpotent radical, and the sum error is added to one lift "
                    + "without changing any augmentation. Minus-one membership is retained "
                    + "as a source assumption; the proof does not need it.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("minac-nguyen-tan-question-3-5"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mnt-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source)
                : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SumPropertyFormula()
    {
        var R = F.Id("R"); var S = F.Id("S"); var n = F.Id("n");
        var membership = All("i", Call("Fin", n), In(Call("a", F.Id("i")), S));
        var equality = Eq(Call("sum", F.Id("a")), F.Id("r"));
        var witness = Ex("a", Call("Function", Call("Fin", n), R), And(membership, equality));
        var definition = Iff(Call("HasNSumProperty", S, n), All("r", R, witness));
        return All("R", F.Id("Type"), Instance("AddCommMonoid", R,
            All("S", Call("Set", R), All("n", F.Id("Nat"), definition))));
    }

    private static Formula AugmentationFormula()
    {
        var K = F.Id("F"); var G = F.Id("G"); var x = F.Id("x");
        return FieldGroup(All("x", Call("MonoidAlgebra", K, G),
            Eq(Call("augmentation", K, G, x), Call("supportSum", Call("coeff", x)))));
    }

    private static Formula UnitSubgroupFormula()
    {
        var K = F.Id("F"); var G = F.Id("G"); var U = F.Id("U"); var v = F.Id("v");
        return FieldGroup(All("U", Call("Subgroup", Call("Units", K)),
            All("v", Call("Units", Call("MonoidAlgebra", K, G)),
                Iff(In(v, Call("augmentationUnitSubgroup", K, G, U)),
                    In(Call("mapUnit", Call("augmentation", K, G), v), U)))));
    }

    private static Formula ResultFormula()
    {
        var K = F.Id("F"); var G = F.Id("G"); var U = F.Id("U"); var n = F.Id("n");
        var augUnits = Call("unitValues", Call("augmentationUnitSubgroup", K, G, U));
        var body = All("U", Call("Subgroup", Call("Units", K)),
            Implies(In(Seq(Minus, F.D(1)), U),
                All("n", F.Id("Nat"), Implies(Lt(F.D(2), Call("card", K)),
                    Implies(Le(F.D(2), n),
                        Implies(Call("HasNSumProperty", Call("unitValues", U), n),
                            Call("HasNSumProperty", augUnits, n)))))));
        return FieldGroup(Instance("Finite", K, Instance("Finite", G, body)));
    }

    private static Formula FieldGroup(Formula body) =>
        All("F", F.Id("Type"), All("G", F.Id("Type"),
            Instance("Field", F.Id("F"), Instance("Group", F.Id("G"), body))));
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula In(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
