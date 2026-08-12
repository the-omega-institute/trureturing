using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class ShadowOfIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A named nonnegative remainder turns an exact identity into its shadow inequality, with Cauchy-Schwarz as the kinematic instance.",
        H("Shadows of Identities"),
        Blocks(
            Paragraph(Text(
                "An inequality is the shadow of an identity when its slack is not merely known to be "
                + "nonnegative: the slack is identified with a named explicit remainder supplied by "
                + "the identity. IsShadow records both parts. This distinction is the point of the "
                + "definition; dropping the name would retain only an ordinary inequality.")),
            Paragraph(Text(
                "The definition earns its place in the kinematic instance. The frozen Lagrange-Gram "
                + "identity supplies the exact Cauchy-Schwarz slack, and its explicit double sum is "
                + "proved locally nonnegative as a nested sum of squares. Cauchy-Schwarz is then "
                + "obtained solely by applying is_shadow_le; it is not reproved by an independent "
                + "inequality argument.")),
            Paragraph(Text(
                "The proposed statistical instance was dropped honestly. The suggested identity "
                + "0 = 0 - (-KL) simplifies to 0 = KL and is false in general. Writing IsShadow 0 KL "
                + "KL would only repackage Gibbs nonnegativity together with the tautology KL - 0 = KL, "
                + "with no separate identity producing the slack. Only the kinematic family is "
                + "instantiated here.")),
            Paragraph(Text(
                "The source note also asserts that the statistical and kinematic families descend "
                + "respectively from normalization and positivity, and that both reduce to one source. "
                + "That structural claim is not formalized in this module. No physical or "
                + "information-theoretic interpretation is claimed.")),
            Describe.Lean(
                DescribeId.Create("a-shadow-names-an-explicit-nonnegative-remainder"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/ShadowOfIdentity.IsShadow"),
                H("A shadow names an explicit nonnegative remainder"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("IsShadow")), F.Open,
                    F.Id("lhs"), F.Comma, F.Sp, F.Id("rhs"), F.Comma, F.Sp,
                    F.Id("remainder"), F.Close, F.Sp, F.Colon, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Prop")), F.Sp, F.Eq, F.Sp,
                    F.Open, F.Id("rhs"), F.Sp, F.Minus, F.Sp, F.Id("lhs"), F.Close,
                    F.Sp, F.Eq, F.Sp, F.Id("remainder"), F.Sp, F.Land, F.Sp,
                    F.D(0), F.Le, F.Sp, F.Id("remainder")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IsShadow lhs rhs remainder asserts the exact slack equation rhs - lhs = remainder "
                    + "and the nonnegativity 0 <= remainder. The named quantity is therefore part of "
                    + "the content, not an after-the-fact label for an already known inequality."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("a-shadow-implies-its-inequality"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/ShadowOfIdentity.is_shadow_le"),
                H("A shadow implies its inequality"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("lhs"), F.Comma, F.Sp,
                    F.Id("rhs"), F.Comma, F.Sp, F.Id("remainder"), F.Sp,
                    F.Operatorname, F.Grp(F.Id("IsShadow")), F.Open,
                    F.Id("lhs"), F.Comma, F.Sp, F.Id("rhs"), F.Comma, F.Sp,
                    F.Id("remainder"), F.Close, F.Sp, F.Rightarrow, F.Sp,
                    F.Id("lhs"), F.Sp, F.Le, F.Sp, F.Id("rhs")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Once the explicit remainder is nonnegative, the identity rhs - lhs = remainder "
                    + "gives lhs <= rhs. This extraction discards only the named remainder; it does "
                    + "not replace the identity with an unmotivated inequality."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-lagrange-gram-cauchy-schwarz-slack-is-a-shadow"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/ShadowOfIdentity.lagrange_gram_is_shadow"),
                H("The Lagrange-Gram slack is an explicit shadow remainder"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("IsShadow")), F.Sp,
                    F.Open, F.Open, F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("u"), F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("v"), F.Underscore, F.Grp(F.Id("i")), F.Close,
                    F.Caret, F.Grp(F.D(2)), F.Close, F.Comma, F.Sp,
                    F.Open, F.Open, F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("u"), F.Underscore, F.Grp(F.Id("i")), F.Caret,
                    F.Grp(F.D(2)), F.Close, F.Sp, F.Times, F.Sp,
                    F.Open, F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("v"), F.Underscore, F.Grp(F.Id("i")), F.Caret,
                    F.Grp(F.D(2)), F.Close, F.Close, F.Comma, F.Sp,
                    F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)), F.Sp,
                    F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Sum, F.Underscore, F.Grp(F.Id("j")), F.Sp,
                    F.Open, F.Id("u"), F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("v"), F.Underscore, F.Grp(F.Id("j")), F.Sp, F.Minus, F.Sp,
                    F.Id("u"), F.Underscore, F.Grp(F.Id("j")), F.Sp,
                    F.Id("v"), F.Underscore, F.Grp(F.Id("i")), F.Close,
                    F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set s and real families u and v, the squared dot product is a shadow "
                    + "of the product of the squared-norm sums. The named remainder is one half of the "
                    + "double sum over i and j of (u i v j - u j v i)^2. The identity is imported from "
                    + "the frozen Lagrange-Gram module, while nonnegativity is proved here by summing "
                    + "squares and dividing by the positive constant two."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("cauchy-schwarz-follows-only-by-shadow-extraction"),
                DeclarationHandle.Create("D5/S3/DivergenceSupport/ShadowOfIdentity.cauchy_schwarz_of_lagrange_gram"),
                H("Cauchy-Schwarz follows by extracting the shadow inequality"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Open, F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("u"), F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("v"), F.Underscore, F.Grp(F.Id("i")), F.Close,
                    F.Caret, F.Grp(F.D(2)), F.Sp, F.Le, F.Sp,
                    F.Open, F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("u"), F.Underscore, F.Grp(F.Id("i")), F.Caret,
                    F.Grp(F.D(2)), F.Close, F.Sp, F.Times, F.Sp,
                    F.Open, F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
                    F.Id("v"), F.Underscore, F.Grp(F.Id("i")), F.Caret,
                    F.Grp(F.D(2)), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Cauchy-Schwarz is derived solely by applying is_shadow_le to the frozen "
                    + "Lagrange-Gram shadow. The theorem therefore demonstrates why the definition "
                    + "carries mathematical weight: the explicit remainder and its local positivity "
                    + "are the bridge from the identity to the inequality."))),
                DescribeRole.Theorem
            ))));
}
