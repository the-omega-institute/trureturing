using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class SecondOrderEulerFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergent local second-order factors assemble into the corresponding Euler product.",
        H("Second-Order Euler Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("second-order-euler-factorization"),
                DeclarationHandle.Create("D5/S3/Factorization/SecondOrderEulerFactorization.second_order_euler_factorization"),
                H("Local second-order factors assemble globally"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Prod, Underscore, F.Id("i"), Sp, F.Id("L"), Underscore, F.Id("i"),
                                    Sp, Eq, Sp,
                                    Open, Prod, Underscore, F.Id("i"), Sp, F.Id("A"), Underscore,
                                    F.Id("i"), Close,
                                    Open, Prod, Underscore, F.Id("i"), Sp, F.Id("B"), Underscore,
                                    F.Id("i"), Close,
                                    Open, Prod, Underscore, F.Id("i"), Sp, F.Id("C"), Underscore,
                                    F.Id("i"), Close, Sp,
                                    Operatorname, Grp(F.Id("exp")),
                                    Open, Sum, Underscore, F.Id("i"), Sp, F.Id("H"), Underscore,
                                    F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Suppose every local Euler factor is the product of two leading "
                                        + "factors, a reciprocal factor, and the exponential of a remainder. "
                                        + "If the three factor products converge and the remainders have a "
                                        + "sum, then the product of the local factors equals the product of "
                                        + "the three global factors times the exponential of the remainder "
                                        + "sum. The reciprocal product is supplied with its own convergence "
                                        + "witness, so the statement does not silently divide by a possibly "
                                        + "zero limit.")),
                                    Paragraph(Text(
                                        "This is the convergence-witness transport behind the source atom's "
                                        + "second-order factorization. The pinned library has the required "
                                        + "pieces but no exact assembled declaration: HasProd.mul composes "
                                        + "the leading products, HasSum.cexp turns the remainder sum into an "
                                        + "exponential product, HasProd.congr_fun applies the local identity, "
                                        + "and HasProd.unique identifies the global limit. The declaration is "
                                        + "therefore a thin honest wrapper over those general results."))),
                DescribeRole.Theorem
            ))));
}
