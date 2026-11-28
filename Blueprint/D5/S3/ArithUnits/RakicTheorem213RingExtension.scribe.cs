using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class RakicTheorem213RingExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/RakicTheorem213RingExtension.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/rakic2026squareanalogue");

    private static readonly Formula R = F.Id("R");
    private static readonly Formula A = F.Id("a");
    private static readonly Formula B = F.Id("b");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");
    private static readonly Formula U = F.Id("u");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rakić's difference criterion for group inverses extends to unital associative rings.",
        H("Group inverses of differences"),
        Blocks(
            Describe.Lean(DescribeId.Create("group-inverse"),
                DeclarationHandle.Create(Prefix + "GroupInv"), H("Group inverse"),
                StatementSource.FromAuthor(Disp(
                    Quantify(Seq(X, Comma, Y),
                        Equivalent(Apply("GroupInv", X, Y),
                            Paren(Conjoin(Equal(Seq(X, Y, X), X), Apply("FD", X, Y))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A group inverse is a finite Drazin inverse with zero remainder. Equivalently, "
                    + "the two elements satisfy both reflexive inverse equations and commute."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minus-order"),
                DeclarationHandle.Create(Prefix + "MinusOrder"), H("Minus relation"),
                StatementSource.FromAuthor(Disp(
                    Quantify(Seq(A, Comma, B),
                        Equivalent(Apply("MinusOrder", A, B),
                            Paren(Seq(Exists, Sp, Binder(U, R), Comma, Sp,
                                Conjoin(Equal(Seq(A, U, A), A), Equal(Seq(U, A), Seq(U, B)),
                                    Equal(Seq(A, U), Seq(B, U))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The same inner-inverse witness gives the two equalities comparing the inputs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-criterion"),
                DeclarationHandle.Create(Prefix + "result"), H("Rakić's ring extension question"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The criterion applies to every unital associative ring, including the zero ring. "
                        + "The witnesses alpha and beta are group inverses of a and b, respectively.")),
                    Paragraph(Text(
                        "Put p = b beta, e = a alpha and c = b minus a. The minus relation is equivalent "
                        + "to absorption of a by p on both sides and a beta a = a. In that case c beta c = c. "
                        + "The inner inverse equation for the difference forces c alpha c = 0. "
                        + "The outer inverse and commuting equations then imply e b e = a and "
                        + "b squared times e = e times b squared = a squared. These yield the first "
                        + "three cubic identities. Applying the argument to c and its complement a "
                        + "gives the difference-of-cubes identity.")),
                    Paragraph(Text(
                        "Conversely, the first three identities give the absorption equations "
                        + "and a beta a = a. Expanding the difference-of-cubes identity and multiplying "
                        + "on the left by beta squared gives c alpha c = 0. Substitution yields "
                        + "both inverse equations and commutation for the difference."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rakic-2026-theorem-2-13-ring-extension"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var inverseCondition = Conjoin(Apply("MinusOrder", A, B),
            Apply("GroupInv", Subtract(B, A), Subtract(Beta, Alpha)));
        var cubicCondition = Conjoin(
            Equal(Power(A, 3), Seq(A, B, A)),
            Equal(Power(A, 3), Seq(A, Power(B, 2))),
            Equal(Power(A, 3), Seq(Power(B, 2), A)),
            Equal(Power(Paren(Subtract(B, A)), 3), Subtract(Power(B, 3), Power(A, 3))));
        return Quantify(Seq(A, Comma, Alpha, Comma, B, Comma, Beta),
            Seq(Apply("GroupInv", A, Alpha), Sp, To, Sp, Apply("GroupInv", B, Beta), Sp, To, Sp,
                Paren(Equivalent(Paren(inverseCondition), Paren(cubicCondition)))));
    }

    private static Formula Quantify(Formula variables, Formula body) =>
        Seq(Forall, Sp, Binder(R, Name("Type")), Sp, OpenBracket, Apply("Ring", R), CloseBracket, Sp,
            Binder(variables, R), Comma, Sp, body);

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula Paren(Formula body) => Seq(Open, body, Close);
    private static Formula Binder(Formula name, Formula type) => Paren(Seq(name, Colon, Sp, type));
    private static Formula Power(Formula value, int degree) => new Formula.Power(value, Num(degree));
    private static Formula Equivalent(Formula lhs, Formula rhs) => Seq(lhs, Sp, Iff, Sp, rhs);
    private static Formula Conjoin(params Formula[] clauses) => Seq(clauses
        .SelectMany((clause, index) => index == 0 ? new[] { clause } : new[] { Sp, Land, Sp, clause })
        .ToArray());
}
