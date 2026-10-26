using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class FibonacciGainRaySuffixDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ConceptDynamics/Experiment/FibonacciGainRaySuffix";
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A universally collinear fixed gain readout vanishes on the identical-row family "
        + "when fewer than a full coefficient dimension of sensitive reads are available.",
        H("Short Sensitive Suffixes of Fibonacci Gain Readouts"),
        Blocks(
            Describe.Lean(DescribeId.Create("fibonacci-identical-row-source"),
                DeclarationHandle.Create(Owner + ".source"), H("Identical-row normalized source"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("Ptheta"), Eq,
                    Call("rows", Seq(Num(1), Minus, F.Id("theta")), F.Id("theta"),
                        Seq(Num(1), Minus, F.Id("theta")), F.Id("theta"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real theta, the two rows are (1-theta,theta). "
                    + "For 0<theta<1 this is a strictly positive rank-one matrix of trace one. "
                    + "The native swap J fixes this matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fibonacci-whole-polynomial-gain"),
                DeclarationHandle.Create(Owner + ".gain"), H("The whole ordinary polynomial"),
                StatementSource.FromAuthor(Disp(Seq(Call("g", F.Id("beta"), F.Id("t")), Eq,
                    Call("sum", Seq(F.Id("j"), Lt, F.Id("m")), Seq(Seq(F.Id("beta"), Underscore, Grp(F.Id("j"))),
                        Seq(F.Id("t"), Caret, Grp(F.Id("j")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient vector beta has m real entries in ascending "
                    + "power order, including the constant coefficient. Only beta=0 is excluded "
                    + "from the world family. Lower degree and constant polynomials, arbitrary "
                    + "coefficient signs, sampled roots, and repeated roots remain in scope."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fibonacci-native-gain-reads"),
                DeclarationHandle.Create(Owner + ".reads"), H("All immediate original-clock reads"),
                StatementSource.FromAuthor(Disp(Seq(Seq(F.Id("z"), Underscore, Grp(F.Id("i"))), Eq,
                    Call("g", F.Id("beta"), F.Id("i")),
                    Call("tr", Seq(Seq(F.Id("A"), Underscore, Grp(F.Id("i"))), F.Id("Ptheta"))),
                    Plus, F.Id("delta")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal chronological Boolean word w has N-1 actions: "
                    + "false is M with rows (0,1),(1,1), and true is J with rows (0,1),(1,0). "
                    + "A_i is SelfCalibratingRulings.matrix(w.take i), so A_0=I and "
                    + "A_(i+1)=E_(i+1)A_i. Each clock i=0,...,N-1 is acquired exactly once. "
                    + "The same whole gain, initial source, and arbitrary real drift delta "
                    + "occur in every read; no reset, skipped read, or clock change is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fibonacci-short-sensitive-suffix-annihilation"),
                DeclarationHandle.Create(Owner + ".short_suffix_annihilates"),
                H("Universal collinearity forces zero on the same family"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("ShortSuffix", F.Id("w"), F.Id("N"), F.Id("m")), Land,
                    Call("UniversalCollinearity", F.Id("C"), F.Id("Zw"), F.Id("Xid")),
                    Rightarrow, Forall, Sp, F.Id("xi"), InMacro, F.Id("Xid"), Comma, Sp,
                    F.Id("C"), Call("Zw", F.Id("xi")), Eq, Num(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every integer d>=1, put m=d+1. For every N>=1, every "
                        + "literal word w of length N-1, and each fixed real m by N matrix C, "
                        + "ShortSuffix means either w contains no M, including w empty, or "
                        + "there are arbitrary literal lists p,q and an original clock n with "
                        + "w=p followed by M followed by q, p pure J, n=length(p)+1, and N-n<m. "
                        + "The initial read counts, and n is not renumbered.")),
                    Paragraph(Text("Xid consists of every theta in (0,1), every nonzero beta "
                        + "in real m-space, and every real delta. The matrix C is fixed before "
                        + "these universal quantifiers. UniversalCollinearity means that at "
                        + "each such point there exists a real scalar s with C Zw=s beta. "
                        + "Zero and both signs of s are permitted. The conclusion is C Zw=0 "
                        + "at every point of this same Xid, so universal collinearity cannot "
                        + "also yield a successful nonzero output anywhere on this family.")),
                    Paragraph(Text("Native chronological induction shows that A_i(1,1) has "
                        + "positive coordinates. They are both one before the first M and "
                        + "unequal after it: J interchanges them, while M maps (u,v) to (v,u+v). "
                        + "Writing b_i=v_i-u_i gives tr(A_i Ptheta)=u_i+theta b_i. "
                        + "Varying the whole gain and drift annihilates C times the all-ones "
                        + "vector and makes the coefficient map scalar. Two interior theta "
                        + "values identify its constant and sensitivity scalar matrices.")),
                    Paragraph(Text("The sensitivity diagonal has fewer than m nonzero entries. "
                        + "Its scalar matrix therefore has scalar zero by the pinned matrix-rank "
                        + "bounds. The first matching number of original-clock power moments "
                        + "then annihilates each supported column of C, using the frozen finite "
                        + "Vandermonde readout injectivity theorem. At every remaining clock "
                        + "u_i=1; the constant-polynomial column and drift annihilation force "
                        + "the remaining scalar to zero. This also handles a pure-J word and "
                        + "the empty action word without a separate bound on N.")),
                    Paragraph(Text("This is the short-suffix exclusion used by the original "
                        + "adaptive gain-ray argument for pure-J terminal words or a first M "
                        + "after clock m at total budget at most 2m. It proves neither the "
                        + "whole-world completion lemma nor the full adaptive threshold theorem. "
                        + "The zero conclusion is restricted to the identical-row family; "
                        + "it grants no acquisition, calibration, physical-cost, or "
                        + "empirical-performance entitlement."))), DescribeRole.Theorem))));
}
