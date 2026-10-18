using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class BinaryRenyiCombiningDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hircheguantomamichel2023renyicombining");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Renyi entropy and binary convolution supply shared scalar definitions for information combining.",
        H("Binary Renyi combining"),
        Blocks(
            Node("binary-entropy", "hRenyi", "Binary Renyi entropy",
                EntropyFormula(),
                "Page 2, before Theorem I.1: \"In the following, we denote the binary Rényi entropy "
                    + "as hα.\" The formula is the binary specialization of Renyi entropy "
                    + "with natural logarithms. Real powers are explicit in its Lean definition.",
                DescribeRole.Definition),
            Node("binary-convolution", "bconv", "Binary convolution",
                ConvolutionFormula(),
                "The star in the source denotes binary convolution: the probability that "
                    + "two independent binary variables have different values.",
                DescribeRole.Definition),
            Node("bias", "bconv_bias", "Binary convolution multiplies biases",
                Disp(All("p", RealType(), All("q", RealType(),
                    Eqn(Minus2(Num(1), Times2(Num(2), Call("bconv", F.Id("p"), F.Id("q")))),
                        Times2(Minus2(Num(1), Times2(Num(2), F.Id("p"))),
                            Minus2(Num(1), Times2(Num(2), F.Id("q")))))))),
                "The polynomial identity holds for all real inputs. For binary probabilities, "
                    + "it expresses the bias of the XOR as the product of the two input biases. "
                    + "The order-three equality and the Hirche concavity argument both use this identity.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string name, string title,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("binary-renyi-" + id),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Plus2(Formula left, Formula right) => Add(left, right);
    private static Formula Minus2(Formula left, Formula right) => Subtract(left, right);
    private static Formula Times2(Formula left, Formula right) => Multiply(left, right);
    private static Formula Divide(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula LogOf(Formula x) => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id("Real"), Dot, F.Id("log"))), [x]);

    private static Formula EntropyFormula()
    {
        Formula alpha = F.Id("alpha"), p = F.Id("p");
        return Disp(All("alpha", RealType(), All("p", RealType(),
            Eqn(Call("hRenyi", alpha, p), Times2(Divide(Num(1), Minus2(Num(1), alpha)),
                LogOf(Plus2(Pow(p, alpha), Pow(Minus2(Num(1), p), alpha))))))));
    }

    private static Formula ConvolutionFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        return Disp(All("p", RealType(), All("q", RealType(), Eqn(Call("bconv", p, q),
            Plus2(Times2(p, Minus2(Num(1), q)), Times2(Minus2(Num(1), p), q))))));
    }

}
