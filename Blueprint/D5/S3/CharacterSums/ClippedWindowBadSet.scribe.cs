using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class ClippedWindowBadSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second moments control exceptional points on a full clipped-sum window",
        H("Arbitrary real knots and complex coefficient arrays"),
        Blocks(
            Paragraph(Text("Let T be a finite set in any index type, "
                + "h(n) real with no sign restriction, "
                + "and a(n,q) an arbitrary complex coefficient array. Define "
                + "S(y,q,k) = sum over n in T of min(1,y/h(n)) k(n) a(n,q). "
                + "No bound on a is required. The multiplier k has modulus at most one on T.")),
            Describe.Lean(DescribeId.Create("clipped-window-bad-set"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/ClippedWindowBadSet.clipped_window_bad_set"),
                H("Quantitative exceptional-set bound on every window above two"),
                StatementSource.FromAuthor(F.Disp(new Formula.Relation(
                    F.Id("Bcard"), FormulaRelationOperator.LessThanOrEqual,
                    F.Seq(new Formula.FunctionCall(FormulaIdentifier.Create("min"),
                        [F.D(1), F.Id("M")]), F.Sp, F.Id("Pcard"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This repository derivation strengthens Alpöge's formalized "
                        + "QH.bad_share (Q/BadShare.lean). At the pinned revision its file is "
                        + "src/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean in "
                        + "https://github.com/the-omega-institute/riemann-hypothesis at commit "
                        + "c7d25b3bfd7906388bb8eb0774e027a2b756a7b6. It permits arbitrary index "
                        + "types, arbitrary real knots, complex coefficient arrays and d > 0, "
                        + "with an explicit decay rate for every Y ≥ 2. A zero knot contributes "
                        + "zero because real division by zero is zero. Put H = max(X,1)+1. "
                        + "Replace each nonpositive knot by H and its coefficient by "
                        + "H/h(n) times a(n,q), leaving positive knots unchanged. For "
                        + "y in [Y,X], min(1,y/H) H/h(n) = min(1,y/h(n)) at every "
                        + "nonpositive knot. Thus every multiplier sum is unchanged, and "
                        + "the moment and bad-point hypotheses pass to positive knots.")),
                    Paragraph(Text("For C >= 0, tau > 0, d > 0 and every Y >= 2, take any X, "
                        + "all finite T and arbitrary real knots h, every coefficient array a and "
                        + "finite sets B contained in P. Assume that for all y in [Y,X] and "
                        + "every multiplier kprime bounded in modulus by one on T, "
                        + "the sum over q in P of "
                        + "|S(y,q,kprime)| squared is at most C y log(y) |P|. "
                        + "If each q in B has some y in [Y,X] with "
                        + "|S(y,q,k)| >= d y^(1/2+tau), then |B| <= min(1,M) |P|, where "
                        + "M = 8 C Y^(-tau) / (d squared times tau times (1-2^(-tau))). "
                        + "The bound is uniform in the upper endpoint and the finite array.")),
                    Paragraph(Text("For the positive replacement knots the right derivative is "
                        + "the sum of k(n)a(n,q)/h(n) "
                        + "over h(n) > y. Multiplication by y makes it another allowed "
                        + "clipped sum, using the multiplier masked to h(n) > y. "
                        + "The fundamental theorem of calculus and interval Cauchy-Schwarz "
                        + "bound "
                        + "the sum of squares at independently selected points of a block "
                        + "[u,v], with v <= 2u, by 4 C u log(2u) |P|. "
                        + "Threshold counting gives at most "
                        + "8 C u^(-tau) |P| / (d squared times tau) bad indices.")),
                    Paragraph(Text("The interval square estimate directly uses "
                        + "D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer."
                        + "interval_cauchy_schwarz after translation by the lower endpoint.")),
                    Paragraph(Text("Assign each bad witness to a binary block starting "
                        + "at 2^j Y. Summing the geometric series gives the explicit bound "
                        + "8 C Y^(-tau) |P| / (d squared times tau times (1-2^(-tau))). "
                        + "Combining with B contained in P gives min(1,M) |P|. "
                        + "The coefficient M tends to zero. For each eta > 0 there is Y0 "
                        + "depending only on C, tau, eta and d, so every Y >= Y0 gives "
                        + "|B| <= eta |P|. The truncation and upper endpoint may vary freely.")),
                    Paragraph(Text("For the quadratic Mangoldt test, take T = {1,...,floor Z}, "
                        + "h(n) = n and a(n,q) = Lambda(n) times the Jacobi symbol (n/q). "
                        + "Taking d = 1/2 gives the full-window bad-set bound. "
                        + "The existing real-valued twistedBy sum has the same factors; "
                        + "the present array also permits complex multipliers. "
                        + "A single-point moment estimate is insufficient: the derivative "
                        + "mask and the binary block summation are both used."))),
                DescribeRole.Theorem))));
}
