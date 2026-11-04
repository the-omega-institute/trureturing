using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class PeriodicBoundarySchroderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/oeis2024a376317");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two periodic shifts of Kurkov's original array have the large Schroder diagonal.",
        H("Periodic Boundary Arrays And Schroder Numbers"),
        Blocks(
            Note("P", "The original total array",
                "For an arbitrary natural-valued shift f, set P_f(0,m)=1 for every "
                + "natural m, with this clause taking priority. For n positive and "
                + "m<=n set P_f(n,m)=P_f(n-1,m). For n positive and m>n set "
                + "P_f(n,m)=P_f(n,m-1)+P_f(n-1,m+f(m-n)). All indices and values "
                + "are natural numbers. Lexicographic recursion on (n,m) terminates "
                + "even when the lower-row column increases; no bound on f is assumed.",
                AssessedProvenance.FromLiterature(Source)),
            Note("f2", "The period-two shift", "Set f2(d)=d mod 2.",
                AssessedProvenance.FromLiterature(Source)),
            Note("f3", "The period-three shift",
                "Set f3(d)=0 when d mod 3 is zero, and f3(d)=1 otherwise.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("periodic-boundary-schroder-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The two exact diagonals"), StatementSource.FromAuthor(Identity()),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "The statement includes every natural n, starting at zero, and "
                        + "both source shifts simultaneously. The target is Mathlib's "
                        + "unshifted Nat.largeSchroder, the sequence A006318. In particular "
                        + "P_f(1,1)=1. A376388 repeats the same source conjecture; it does "
                        + "not supply a separate question or a second resolution.")),
                    Paragraph(Text(
                        "Write C_f(n,d)=P_f(n,n+d). The original equations give "
                        + "C_f(0,d)=1, C_f(n+1,0)=C_f(n,1), and "
                        + "C_f(n+1,d+1)=C_f(n+1,d)+C_f(n,d+2+f(d+1)). "
                        + "Thus P_f(n+1,n+1)=C_f(n,1). The original below-diagonal "
                        + "branch remains in the definition of P; no reconstructed "
                        + "or truncated array replaces it.")),
                    Paragraph(Text(
                        "Work in rational formal power series. A family H with every "
                        + "constant coefficient one, H(0)=1+xH(1), and "
                        + "H(d+1)=H(d)+xH(d+2+f(d+1)) has coefficient n at column d "
                        + "equal to C_f(n,d). The proof inducts first on n with its "
                        + "hypothesis quantified over all columns. At degree n+1 the "
                        + "zero column uses degree n of column one. Induction on d "
                        + "then uses the previous column at degree n+1 and the shifted "
                        + "column at degree n. This supplies the entire infinite family "
                        + "without convergence or a finite-column cutoff.")),
                    Paragraph(Text(
                        "Let S be Mathlib's largeSchroderSeries mapped to the rationals. "
                        + "The original owner SchroderIntegralEGF.R supplies S; its "
                        + "R_eq and R_zero give S=1+xS+xS^2 and constant coefficient "
                        + "one. For f2 take H(2j)=(1+xS)S^j and "
                        + "H(2j+1)=S^(j+1). The even and odd recurrences follow from "
                        + "this quadratic identity; the odd branch includes d=1.")),
                    Paragraph(Text(
                        "For f3 put R=(S^2+S)/2 in the rational series ring. The same "
                        + "quadratic gives R-S=xSR and S^2-R=xSR. Set H(0)=1+xS, "
                        + "H(3j+1)=SR^j, H(3j+2)=R^(j+1), and H(3j+3)=S^2R^j. "
                        + "The column-one recurrence is checked separately; the three "
                        + "positive residue branches use the two displayed identities. "
                        + "Every constant coefficient is one and H(1)=S. All exponents "
                        + "are natural; no negative exponent or natural division by two "
                        + "is used. The coefficient-identification argument applies "
                        + "to both families. Extracting coefficient n and using the "
                        + "existing injective natural-to-rational cast proves the two "
                        + "equalities. A separate integrality assumption on R is unnecessary.")),
                    Paragraph(Text(
                        "The source is Kurkov's conjecture in OEIS A376317 revision 25, "
                        + "introduced in revision 15; the original wording and bounded "
                        + "literature search are recorded in the cited Library note. "
                        + "OEIS attribution and its CC-BY-SA-4.0 license apply to source "
                        + "text. The proof is a repository derivation reusing Mathlib's "
                        + "Apache-2.0 Schroder series theorem. The literature search "
                        + "has a bounded scope and does not establish global priority."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a376317-kurkov-periodic-boundary-schroder"),
                    ResolutionKind.Proved)))));

    private static Formula Identity() => Disp(Seq(
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Entry("f2"), Sp, Eq, Sp, Target(), Sp, Land, Sp,
        Entry("f3"), Sp, Eq, Sp, Target()));

    private static Formula Entry(string f) => new Formula.Apply(
        new Formula.Subscript(F.Id("P"), F.Id(f)),
        [Seq(F.Id("n"), Plus, D(1)), Seq(F.Id("n"), Plus, D(1))]);

    private static Formula Target() => new Formula.Apply(F.Id("largeSchroder"), [F.Id("n")]);

    private static DocumentBlock Note(string name, string title, string prose,
        AssessedProvenance provenance) => Describe.Remark(
        DescribeId.Create("periodic-boundary-schroder-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), provenance,
        Blocks(Paragraph(Text(prose))));
}
