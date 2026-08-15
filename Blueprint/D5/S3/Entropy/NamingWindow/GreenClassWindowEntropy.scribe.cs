using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class GreenClassWindowEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent coordinate laws induce normalized naming-window laws whose Shannon entropy " +
        "is additive and bounded by naming dimension, with equality for uniform coordinates.",
        H("Green-Class Window Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-law-is-the-coordinate-product"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw"),
                H("A window law is the product of its coordinate masses"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    F.Id("p"), Comma, Sp, F.Id("u"), Close,
                    Sp, Eq, Sp,
                    Prod, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Underscore, Grp(F.Id("i")), Open,
                    F.Id("u"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite coordinate set, the mass of a window assignment u is the " +
                        "product of the coordinate masses p_i(u_i). The definition imposes no " +
                        "normalization or positivity assumptions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coordinate-law-is-singleton-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.coordLaw"),
                H("A coordinate law is the real singleton mass"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("coordLaw")), Open,
                    F.Id("mu"), Comma, Sp, F.Id("i"), Comma, Sp, F.Id("a"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("toReal")), Open,
                    F.Id("mu"), Underscore, Grp(F.Id("i")), OpenBrace,
                    F.Id("a"), CloseBrace, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a family of alphabet measures mu_i, coordLaw reads the singleton mass " +
                        "of a letter as a real number. Probability measures make each finite " +
                        "coordinate law normalized."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-coordinates-give-a-normalized-window-law"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw_sum_eq_one"),
                H("Normalized coordinate laws give a normalized window law"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("u")), Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    F.Id("p"), Comma, Sp, F.Id("u"), Close,
                    Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Summing the coordinate product over all finite window assignments factors " +
                        "as the product of the coordinate sums. If every coordinate sum is one, the " +
                        "window sum is one as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-entropy-is-additive"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_windowLaw"),
                H("Window entropy is the sum of coordinate entropies"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close, Close,
                    Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The negative-log product identity expands each assignment's entropy term " +
                        "into one contribution per coordinate. Finite sum-product interchange and " +
                        "coordinate normalization remove every complementary product.")),
                    Paragraph(Text(
                        "The result is the finite Shannon entropy in nats of the product window law, " +
                        "equal to the sum of the coordinate entropies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("green-class-mass-is-a-window-law"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.greenClass_toReal_eq_windowLaw"),
                H("Green-class mass is the window law of its pinned content"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("toReal")), Open,
                    F.Id("mu"), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("mu"), Close,
                    Comma, Sp, Grp(F.Id("t"), Sp, Mid, Sp, F.Id("S")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The infinite product measure of the green class G(S,t) is the finite " +
                        "product of the pinned singleton masses. Converting those masses to real " +
                        "numbers identifies that product with the corresponding window law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-entropy-is-bounded-by-naming-dimension"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_windowLaw_le_namingDim"),
                H("Naming dimension bounds green-class window entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("mu"), Close, Close, Close,
                    Sp, Leq, Sp,
                    F.Id("n"), Sp, Times, Sp,
                    Operatorname, Grp(F.Id("namingDim")), Open, F.Id("O"), Close,
                    Sp, Times, Sp, Log, Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let n be the number of pinned coordinates. Entropy additivity reduces the " +
                        "window entropy to n coordinate entropies, and finite-alphabet maximum " +
                        "entropy bounds each summand by log(card O).")),
                    Paragraph(Text(
                        "The identity log(card O) = namingDim(O) log(2) converts that sum into the " +
                        "stated naming-dimension bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-coordinates-attain-the-window-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.shannonEntropy_uniform_windowLaw"),
                H("Uniform coordinate laws attain the naming-dimension bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("u"), Close, Close,
                    Sp, Eq, Sp,
                    F.Id("n"), Sp, Times, Sp,
                    Operatorname, Grp(F.Id("namingDim")), Open, F.Id("O"), Close,
                    Sp, Times, Sp, Log, Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For uniform alphabet measures, every coordinate law has constant mass " +
                        "one over card O and entropy log(card O). Additivity across the pinned " +
                        "coordinates therefore attains the naming-dimension upper bound.")),
                    Paragraph(Text(
                        "This theorem proves attainment only. The converse statement that equality " +
                        "forces every coordinate law to be uniform requires the Gibbs identity and " +
                        "is deliberately outside this module."))),
                DescribeRole.Theorem))));
}
