using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FejerCollisionSecantsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FejerCollisionSecants";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-part secants bound the closed collision band and recover it exactly on a finite right interval.",
        H("Finite recovery of closed collision bands"),
        Blocks(
            Paragraph(Text(
                "Let S be a finite set of indices, x(i) their real frequencies and c(i) their real weights. " +
                "For real radius r, write E(r) for the sum of c(i)c(j) over ordered pairs in S " +
                "with absolute frequency difference at most r. Write L(r) for the sum of " +
                "c(i)c(j) max(0,r-|x(i)-x(j)|) over all ordered pairs.")),
            Describe.Lean(DescribeId.Create("secant-bounds"),
                DeclarationHandle.Create(Owner + ".collision_ramp_secants"),
                H("Secants bracket the closed band"),
                StatementSource.FromAuthor(Bounds()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume c(i)>=0 on S and delta>0. Each pair at distance d<=r contributes exactly " +
                    "delta to the right increment of max(0,r-d), and at most delta to the left " +
                    "increment. A pair at distance d>r contributes zero to the left increment and " +
                    "a nonnegative amount to the right. Multiply by the nonnegative pair weights " +
                    "and sum both inequalities, including pairs on the boundary d=r."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-right-increment"),
                DeclarationHandle.Create(Owner + ".collision_ramp_exact_right"),
                H("Exact right increment for signed data"),
                StatementSource.FromAuthor(Exact()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take delta0 to be the minimum of 1 and the finite set of positive gaps " +
                        "|x(i)-x(j)|-r for pairs outside the closed band. This minimum is positive " +
                        "even when the outer pair set is empty. For every 0<delta<=delta0, every " +
                        "pair is either already within the closed band or at distance at least r+delta. " +
                        "Its right increment is respectively delta or zero. Sum the exact pair identities. " +
                        "The weights may have either sign and r may be any real number.")),
                    Paragraph(Text(
                        "For degree-p frequency sums and multinomial weights, put M(r)=r times " +
                        "the whole-line integral of the angular Fejer kernel K_r(t) multiplied by " +
                        "|S(t)|^(2p), for positive r. The exact triangular Fourier identity gives " +
                        "M(r)=L(r), since r max(0,1-|d|/r)=max(0,r-|d|). Thus for nonnegative " +
                        "original weights and 0<delta<r the two secant bounds hold with M in place " +
                        "of L, and for signed weights the right quotient recovers the closed-band " +
                        "collision mass exactly for all sufficiently small positive delta."))),
                DescribeRole.Theorem))));

    private static Formula R => F.Id("r");
    private static Formula D => F.Id("delta");
    private static Formula E => Call("E", R);
    private static Formula Left => Subtract(Call("L", R), Call("L", Subtract(R,D)));
    private static Formula Right => Subtract(Call("L", Add(R,D)), Call("L", R));
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Bounds() =>
        F.Disp(new Formula.Logic(
            new Formula.Logic(Call("Nonnegative", F.Id("c")), FormulaLogicOperator.And,
                new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, D)),
            FormulaLogicOperator.Implies,
            new Formula.Logic(Le(Left, Multiply(D,E)), FormulaLogicOperator.And, Le(Multiply(D,E), Right))));
    private static Formula Exact()
    {
        Formula d0 = F.Id("deltaZero");
        Formula real = F.Seq(F.Mathbb,F.Grp(F.Id("R")));
        Formula body = new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, d0),
            FormulaLogicOperator.And,
            new Formula.BindMany(FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("delta"),real)],
                new Formula.Logic(new Formula.Logic(
                    new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, D),
                    FormulaLogicOperator.And, Le(D,d0)), FormulaLogicOperator.Implies,
                    Equal(Right,Multiply(D,E)))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("deltaZero"),real)], body));
    }
}
