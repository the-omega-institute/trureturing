using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class EqualRadiusZeroDisksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isolating a zeta zero at a controlled distance from a vertical line",
        H("Equal-radius disks for a zeta zero to the right of one-half"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-radius-disks"),
            DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/EqualRadiusZeroDisks.equal_radius_zero_disks"),
            H("An occupied disk and an empty disk of the same radius"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In the statement s denotes σ, e denotes the loss δ, and q denotes the selected zero ρ. Write β for the real part of the given zero. For σ > 2 and "
                    + "0 < δ < β − 1/2, the two centers have real part σ. The real center has "
                    + "no zeros in its closed disk. The other disk has one zero ρ at a strictly "
                    + "positive distance less than its radius r, where r < σ − β + δ. Every "
                    + "point of either closed disk has real part greater than one-half.")),
                Paragraph(Text("First compare the distance from σ to the nearest zero with "
                    + "σ − β + δ. If the latter is smaller, move the center to the ordinate of "
                    + "the given zero. Otherwise take a nearest zero to σ. It has real part "
                    + "greater than one-half and is nonreal by real-axis nonvanishing. Moving "
                    + "to its ordinate strictly shortens the distance.")),
                Paragraph(Text("For two distinct zeros, equality of distances from the vertical "
                    + "line occurs at most once. At equal ordinates their horizontal distances "
                    + "are distinct, and at distinct ordinates the tie is a single affine "
                    + "equation. The zeros are countable, so some nearby height avoids all "
                    + "ties. The other zeros form a closed set. Choosing the radius below their "
                    + "distance and below both preceding bounds gives the two closed disks."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var zero = F.D(0);
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var c = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var initial = F.Id("z");
        var sigma = F.Id("s");
        var delta = F.Id("e");
        var p = F.Id("p");
        var rho = F.Id("q");
        var r = F.Id("r");
        var w = F.Id("w");
        var distance = Call("dist", p, rho);
        var isZero = Equal(Call("zeta", w), zero);
        var inHalfPlane = Less(half, Call("Re", w));
        var realDisk = ForAll("w", c, Implies(Le(Call("dist", sigma, w), r),
            And(inHalfPlane, new Formula.Relation(Call("zeta", w), FormulaRelationOperator.NotEqual, zero))));
        var occupiedDisk = ForAll("w", c, Implies(Le(Call("dist", p, w), r),
            And(inHalfPlane, Implies(isZero, Equal(w, rho)))));
        var bound = Add(Subtract(sigma, Call("Re", initial)), delta);
        var conclusion = Exists("p", c, Exists("q", c, Exists("r", real,
            And(And(Equal(Call("Re", p), sigma), Equal(Call("zeta", rho), zero)),
                And(And(Less(zero, distance), And(Less(distance, r), Less(r, bound))),
                    And(realDisk, occupiedDisk))))));
        var assumptions = And(Equal(Call("zeta", initial), zero), And(Less(F.D(2), sigma),
            And(Less(zero, delta), Less(delta, Subtract(Call("Re", initial), half)))));
        return F.Disp(ForAll("z", c, ForAll("s", real, ForAll("e", real,
            Implies(assumptions, conclusion)))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula ForAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
