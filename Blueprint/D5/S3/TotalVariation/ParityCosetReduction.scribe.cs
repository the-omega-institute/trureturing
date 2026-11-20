using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityCosetReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform additive noise gives exact quotient laws and preserves total variation under projection.",
        H("Total variation on cosets of the noise image"),
        Blocks(Describe.Lean(
            DescribeId.Create("total-variation-noise-image-quotient"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/ParityCosetReduction.total_variation_noise_image_quotient"),
            H("Quotienting the uniform noise image"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F and A be finite abelian groups, let B and Z be finite types, and let "
                    + "f be an additive homomorphism from F to A. The shift a and the second "
                    + "readout b depend on the state z. The mass of each source pair (z,u) is "
                    + "w(z) divided by the cardinality of F. Its output is (a(z)+f(u),b(z)). "
                    + "The reference is uniform on A against the second-coordinate mass function r.")),
                Paragraph(Text(
                    "Write Q for the quotient of A by the image of f, and project the first "
                    + "coordinate to its coset while preserving the second coordinate. The "
                    + "projected joint law is the pushforward of w by the projected pair of "
                    + "readouts. The projected reference is uniform on Q against r. Translating "
                    + "the uniform source by a preimage of a coset displacement proves that the "
                    + "joint mass is constant inside each fiber. The reference mass is likewise "
                    + "constant there, so projection preserves total variation."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula Ftype = F.Id("F");
        Formula aType = F.Id("A");
        Formula bType = F.Id("B");
        Formula zType = F.Id("Z");
        Formula f = F.Id("f");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula w = F.Id("w");
        Formula r = F.Id("r");
        Formula qType = F.Id("Q");
        Formula projection = F.Id("p");
        Formula joint = Mu;
        Formula reference = Nu;
        Formula q = F.Id("q");
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula u = F.Id("u");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula output = Product(aType, bType);
        Formula reduced = Product(qType, bType);
        Formula sourceMass = new Formula.Fraction(At(w, z), new Formula.Absolute(Ftype));
        Formula fullOutput = Seq(At(a, z), Plus, At(f, u), Comma, At(b, z));
        Formula type = Name("Type");
        Formula left = Seq(x, Dot, D(1));
        Formula right = Seq(x, Dot, D(2));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(Ftype, type), Typed(aType, type), Typed(bType, type),
                Typed(zType, type), Comma),
            Seq(Instance("AddCommGroup", Ftype), Instance("AddCommGroup", aType),
                Instance("Fintype", Ftype), Instance("Fintype", aType),
                Instance("Fintype", bType), Instance("Fintype", zType), Comma),
            Seq(Typed(f, At(Name("AddMonoidHom"), Seq(Ftype, Comma, aType))),
                Typed(a, Arrow(zType, aType)),
                Typed(b, Arrow(zType, bType)), Typed(w, Arrow(zType, real)),
                Typed(r, Arrow(bType, real)), Comma),
            Let(qType, Seq(aType, Slash, At(Name("im"), f))),
            Let(At(projection, Seq(x, Colon, Sp, output)),
                Parenthesized(Seq(OpenBracket, left, CloseBracket, Comma, right))),
            Let(At(joint, Seq(x, Colon, Sp, output)),
                Seq(BoundedSum(Seq(Parenthesized(Seq(z, Comma, u)), Sp, InMacro, Sp,
                    Product(zType, Ftype), Colon, Sp, Parenthesized(fullOutput), Eq, x)),
                    sourceMass)),
            Let(At(reference, Seq(x, Colon, Sp, output)),
                new Formula.Fraction(At(r, right), new Formula.Absolute(aType))),
            Seq(Open, Forall, Sp, Typed(q, reduced), Comma,
                At(Pushforward(projection, joint), q), Eq,
                BoundedSum(Seq(z, Sp, InMacro, Sp, zType, Colon, Sp,
                    At(projection, Seq(At(a, z), Comma, At(b, z))), Eq, q)), At(w, z), Close,
                Sp, Land),
            Seq(Open, Forall, Sp, Typed(q, reduced), Comma,
                At(Pushforward(projection, reference), q), Eq,
                new Formula.Fraction(At(r, Seq(q, Dot, D(2))), new Formula.Absolute(qType)), Close,
                Sp, Land),
            Seq(At(Name("TV"), Seq(joint, Comma, reference)), Eq,
                At(Name("TV"), Seq(Pushforward(projection, joint), Comma,
                    Pushforward(projection, reference))))
        ]));
    }

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Parenthesized(argument));
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, At(Name(name), type), CloseBracket);
    private static Formula Let(Formula value, Formula definition) =>
        Seq(Name("let"), Sp, value, Colon, Eq, definition, Comma);
    private static Formula BoundedSum(Formula index) => new Formula.Subscript(Sum, index);
    private static Formula Pushforward(Formula function, Formula mass) =>
        At(new Formula.Subscript(function, Star), mass);
}
