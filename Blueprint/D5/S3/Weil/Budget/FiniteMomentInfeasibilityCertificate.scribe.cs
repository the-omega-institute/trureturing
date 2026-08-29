using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class FiniteMomentInfeasibilityCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infeasibility of the finite interval-constrained positive-semidefinite moment "
            + "problem excludes every compatible real-axis even positive completion.",
        H("Finite Moment Infeasibility Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-moment-infeasibility-excludes-positive-completion"),
            DeclarationHandle.Create(Prefix + "finite_moment_infeasibility_certificate"),
            H("Finite SDP infeasibility is a strict completion certificate"),
            StatementSource.FromAuthor(CertificateFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The hypotheses expose the completion-to-moment construction, its zero "
                        + "moment, every source interval, and the Toeplitz positivity law.")),
                Paragraph(Text(
                    "A putative real-axis even positive completion with local-source "
                        + "consistency, an in-range resolvent budget, and a Cayley "
                        + "compactification would therefore construct the forbidden SDP "
                        + "witness."))),
            DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula n = F.Id("N");
        Formula index = Call("Fin", Seq(n, Sp, Plus, Sp, D(1)));
        Formula completion = F.Id("C");
        Formula lower = F.Id("Rlower");
        Formula upper = F.Id("Rupper");
        Formula target = F.Id("target");
        Formula tolerance = F.Id("tau");
        Formula toeplitz = F.Id("T");
        Formula realAxis = F.Id("RealAxis");
        Formula even = F.Id("Even");
        Formula positive = F.Id("Positive");
        Formula localSource = F.Id("LocalSource");
        Formula budget = F.Id("B");
        Formula compactification = F.Id("CayleyCompact");
        Formula moments = F.Id("m");
        Formula completionPredicate = Seq(completion, Sp, To, Sp, prop);
        Formula momentVector = Seq(index, Sp, To, Sp, real);
        Formula matrix = Call("Matrix", index, index, real);
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula r = F.Id("R");
        Formula vector = F.Id("v");

        Formula qualifiers = Seq(
            Apply(realAxis, c), Sp, Land, Sp, Apply(even, c), Sp, Land, Sp,
            Apply(positive, c));
        Formula sourceClauses = Seq(
            qualifiers, Sp, Land, Sp, Apply(localSource, c), Sp, Land, Sp,
            lower, Sp, Leq, Sp, Apply(budget, c), Sp, Land, Sp,
            Apply(budget, c), Sp, Leq, Sp, upper, Sp, Land, Sp,
            Apply(compactification, c));
        Formula intervalAtCompletion = Seq(
            Call("abs", Seq(Apply(Apply(moments, c), i), Sp, Minus, Sp,
                Apply(Apply(target, Apply(budget, c)), i))),
            Sp, Leq, Sp, Apply(budget, c), Sp, Cdot, Sp, Apply(tolerance, i));
        Formula intervalAtVector = Seq(
            Call("abs", Seq(Apply(vector, i), Sp, Minus, Sp,
                Apply(Apply(target, r), i))),
            Sp, Leq, Sp, r, Sp, Cdot, Sp, Apply(tolerance, i));
        Formula bridgePremise = Seq(
            qualifiers, Sp, Land, Sp, Apply(localSource, c), Sp, Land, Sp,
            Apply(compactification, c));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, nat, Comma, Sp,
            lower, Comma, Sp, upper, Colon, Sp, real, Comma, RowBreak, Grp(),
            target, Colon, Sp, real, Sp, To, Sp, momentVector, Comma, Sp,
            tolerance, Colon, Sp, momentVector, Comma, RowBreak, Grp(),
            toeplitz, Colon, Sp, Open, momentVector, Close, Sp, To, Sp, matrix,
            Comma, Sp, completion, Colon, Sp, type, Comma, RowBreak, Grp(),
            realAxis, Comma, Sp, even, Comma, Sp, positive, Comma, Sp,
            localSource, Comma, Sp, compactification, Colon, Sp,
            completionPredicate, Comma, RowBreak, Grp(),
            budget, Colon, Sp, completion, Sp, To, Sp, real, Comma, Sp,
            moments, Colon, Sp, completion, Sp, To, Sp, momentVector, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, c, Colon, Sp, completion, Comma, Sp,
            Apply(Apply(moments, c), D(0)), Sp, Eq, Sp, Apply(budget, c), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, c, Colon, Sp, completion, Comma, Sp,
            bridgePremise, Sp, Rightarrow, Sp, Forall, Sp, i, Colon, Sp, index,
            Comma, Sp, intervalAtCompletion, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, c, Colon, Sp, completion, Comma, Sp,
            qualifiers, Sp, Land, Sp, Apply(compactification, c), Sp,
            Rightarrow, Sp, Call("PosSemidef", Apply(toeplitz, Apply(moments, c))),
            Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, Neg, Sp, Exists, Sp, r, Colon, Sp, real, Comma, Sp,
            vector, Colon, Sp, momentVector, Comma, Sp,
            lower, Sp, Leq, Sp, r, Sp, Land, Sp, r, Sp, Leq, Sp, upper,
            Sp, Land, Sp, Apply(vector, D(0)), Sp, Eq, Sp, r, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, i, Colon, Sp, index, Comma, Sp, intervalAtVector,
            Close, Sp, Land, Sp, Call("PosSemidef", Apply(toeplitz, vector)), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Exists, Sp, c, Colon, Sp, completion, Comma, Sp,
            sourceClauses, Dot));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
