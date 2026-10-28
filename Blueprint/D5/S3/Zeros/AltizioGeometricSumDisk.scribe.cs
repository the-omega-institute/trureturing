using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class AltizioGeometricSumDiskDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/AltizioGeometricSumDisk.";
    private static LibraryNoteRef Altizio => LibraryNoteRef.Create("D5/L/Zeros/altizio2025stern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The geometric-sum bound on the closed disk centered at two holds exactly in degrees five, six and seven.",
        H("Altizio's geometric-sum disk classification"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Remark 4"), StatementSource.FromAuthor(Disp(new Formula.Logic(
                    F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Altizio),
                Blocks(Paragraph(Text(
                    "Altizio, p. 20, Remark 4: “One might suspect that |(z)_n| ≥ n|z| more generally "
                    + "whenever z ∈ B. However, numerical evidence suggests that the value "
                    + "min_{z∈B} |(z)_n/z| approaches 2π as n → ∞. It seems that this inequality "
                    + "is true only for n = 5, 6, and 7, but we do not have a proof.” "
                    + "On p. 4, Section 2: “For all positive integers n, we introduce the "
                    + "(non-standard) notation (λ)_n := 1 + λ + ⋯ + λ^{n−1} = "
                    + "(λ^n − 1)/(λ − 1) ∈ ℤ[λ].” The finite sum has indices k = 0, …, n−1; "
                    + "it includes its continuous value n at z = 1. Section 3 writes "
                    + "“B := B_1[2] = {|w − 2| ≤ 1}”. Here n is a positive natural number, "
                    + "z is complex, and the complex absolute value is the norm. The statement "
                    + "classifies the degrees; it makes no assertion about the proposed 2π limit."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The exact set of degrees"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Altizio),
                Blocks(Paragraph(Text(
                    "On the boundary circle, put u = ‖z‖². The power sum zⁿ + conjugate(z)ⁿ "
                    + "obeys a second-order recurrence with sum (u+3)/2 and product u. "
                    + "Subtracting n²u(u−1)/2 gives the squared-norm defect. At degrees 5, 6 "
                    + "and 7 its expansion in u−1 has nonnegative coefficients. The geometric "
                    + "sum is nonzero on the disk, so the maximum modulus principle applied "
                    + "to z divided by that sum extends the boundary estimate to the disk.")),
                    Paragraph(Text(
                    "For every other positive degree, the quadratic coefficient is "
                    + "−n²(n−5)(n−7)/48 ≤ −1/2. Dividing off the first three powers of the "
                    + "polynomial variable leaves a remainder whose coefficient absolute sum "
                    + "bounds its value on [0,1]. Choosing a positive parameter from that sum "
                    + "makes the defect negative and produces a point on the boundary that "
                    + "violates the inequality. This proves both directions for every positive n. "
                    + "The separate bound in Remark 3 and the 2π limit remain unanswered."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("altizio-2025-geometric-sum-disk"),
                    ResolutionKind.Proved)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), z = F.Id("z"), k = F.Id("k");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula center = Parenthesized(Seq(D(2), Colon, Sp, complex));
        Formula disk = new Formula.Apply(Qualified("Metric", "closedBall"), [center, D(1)]);
        Formula member = new Formula.Relation(z, FormulaRelationOperator.MemberOf, disk);
        Formula range = new Formula.Apply(Qualified("Finset", "range"), [n]);
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, range)), Sp,
            new Formula.Power(z, k));
        Formula realN = Parenthesized(Seq(n, Colon, Sp, Mathbb, Grp(F.Id("R"))));
        Formula inequality = new Formula.Relation(
            new Formula.Binary(realN, FormulaBinaryOperator.Multiply, new Formula.Norm(z)),
            FormulaRelationOperator.LessThanOrEqual, new Formula.Norm(sum));
        Formula everyPoint = All("z", complex, new Formula.Logic(member,
            FormulaLogicOperator.Implies, inequality));
        Formula degrees = new Formula.Logic(Equal(n, D(5)), FormulaLogicOperator.Or,
            new Formula.Logic(Equal(n, D(6)), FormulaLogicOperator.Or, Equal(n, D(7))));
        Formula classification = new Formula.Logic(Parenthesized(everyPoint),
            FormulaLogicOperator.Iff, Parenthesized(degrees));
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        return All("n", Seq(Mathbb, Grp(F.Id("N"))), new Formula.Logic(positive,
            FormulaLogicOperator.Implies, Parenthesized(classification)));
    }
}
