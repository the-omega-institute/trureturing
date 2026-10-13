using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class PowerConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consumed general C-star power convexity and its all-Hilbert Jensen adapter.",
        H("PowerConvexity"), Blocks(
            Describe.Lean(DescribeId.Create("power-convexity"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/PowerConvexity.convexOn_rpow"),
                H("Full operator power interval"), StatementSource.FromAuthor(Power()),
                Provenance(), Blocks(Paragraph(Text("For every 1 <= p <= 2, spectral CFC "
                    + "power is convex on the full nonnegative cone of every complete "
                    + "ordered complex C-star algebra, including the trivial algebra. "
                    + "The nontrivial case directly consumes the attributed Physlib "
                    + "LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici; the "
                    + "trivial case is automatic. NonnegSpectrumClass follows from "
                    + "the existing ordered C-star structure. The original upstream "
                    + "integral proof and its consumed helpers live in LownerHeinzCore. "
                    + "They use one common measure for exponent q=p-1 and integrate "
                    + "the entire kernel x times rpowIntegrand01(q,t,x), with norm "
                    + "integrability obtained by constant left multiplication. "
                    + "The polynomial, inverse and constant summands are never "
                    + "integrated separately.")),
                    Paragraph(Text("At p=1 the map is affine. At p=2 the convexity gap "
                    + "is s t times (X-Y)* (X-Y), where s+t=1. Cross products retain "
                    + "their order, so the square identity includes noncommuting "
                    + "inputs. The cone includes zero and singular operators."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-jensen-input"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/PowerConvexity.condIciAll_rpow"),
                H("Uniform all-Hilbert Jensen input"), StatementSource.FromAuthor(Uniform()),
                Provenance(), Blocks(Paragraph(Text("For every universe and every complete "
                    + "nontrivial complex Hilbert space K, x to exponent p is operator "
                    + "convex on the nonnegative real spectrum, continuous on that "
                    + "interval, and zero at zero. Thus it supplies the actual "
                    + "CondIciAll required by the public Jensen perspective theorem. "
                    + "Finite Hilbert-Schmidt convexity is not substituted for this "
                    + "uniform condition.")),
                    Paragraph(Text("The supplier is Physlib revision "
                    + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, "
                    + "Kento Mori and Hayata Yamasaki, Apache-2.0. Pinned Mathlib by "
                    + "Frederic Dupuis supplies shifted-inverse convexity directly. "
                    + "OperatorGeometricMean consumes the uniform condition and "
                    + "LiebAndoTrace consumes its joint-convexity endpoint via the "
                    + "existing public unrestricted-real-exponent phiK bridge. Its matrix "
                    + "transport and reverse Young endpoint optimizer interpolation "
                    + "supply CarlenLiebConvexity. The "
                    + "original Hiai theorem and support boundary remain separate "
                    + "obligations. Native four-slot audit is unfinished under #5214: "
                    + "a faithful enrolled template and realization covering the full "
                    + "C-star and all-Hilbert telescopes, rigid universe reconstruction "
                    + "and variation/sensitivity evidence have not been supplied. "
                    + "No declared_validated status is claimed."))), DescribeRole.Theorem))));

    private static AssessedProvenance Provenance() => AssessedProvenance.FromLiterature(
        LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb"));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Domain() => Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"),
        Comma, Sp, F.Id("A"), Colon, Sp, Call("Type", F.Id("u")), Comma, Esc,
        OpenBracket, Call("CStarAlgebra", F.Id("A")), CloseBracket, Comma, Sp,
        OpenBracket, Call("PartialOrder", F.Id("A")), CloseBracket, Comma, Sp,
        OpenBracket, Call("StarOrderedRing", F.Id("A")), CloseBracket, Comma, Esc);
    private static Formula Cone() => Call("Ici", Seq(D(0), Colon, Sp, F.Id("A")));
    private static Formula Power() => Seq(Domain(), F.Id("p"), Colon, Sp,
        Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, D(1), Le, Sp, F.Id("p"), Le, Sp, D(2),
        Implies, Esc, Call("ConvexOn", Seq(Mathbb, Grp(F.Id("R"))), Cone(),
            Seq(Lambda, Sp, F.Id("X"), Mapsto, Call("rpow", F.Id("X"), F.Id("p")))));
    private static Formula Uniform() => Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"),
        Comma, Sp, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc,
        D(1), Le, Sp, F.Id("p"), Le, Sp, D(2), Implies, Esc,
        Call("CondIciAll", Seq(Lambda, Sp, F.Id("x"), Mapsto, Call("rpow", F.Id("x"), F.Id("p")))));
}
