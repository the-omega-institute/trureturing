using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedResponseArithmeticDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite endpoint-tagged progressions describe exact fixed-response paths.",
        H("Fixed Response Arithmetic"),
        Blocks(
            Describe.Lean(DescribeId.Create("partial-successor"), Handle("successor"),
                H("The instruction successor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A read follows its installed address's reply, an update follows its one "
                    + "successor, and a halt has no successor. The response field is arbitrary; "
                    + "there is no requirement on uninstalled physical addresses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("totalized-step"), Handle("step"),
                H("A separate absorbing sink"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The partial successor is totalized on Option Q. None is absorbing. "
                    + "An iterate ending at some y cannot have visited None earlier. Thus "
                    + "totalization does not add paths leaving a halt or halt self-loops."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("update-weight"), Handle("weight"),
                H("Natural update weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The weight is one at a real update and zero at a read, halt or sink. "
                    + "Its natural prefix Birkhoff sum counts precisely the updates before "
                    + "the endpoint, including the empty prefix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("endpoint-record"), Handle("Record"),
                H("Endpoint and progression coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A record has an Option Q endpoint, a natural offset and a natural increment. "
                    + "An increment of zero gives a singleton weight without moving the endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("computed-records"), Handle("records"),
                H("An executable collision scan"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Given explicit Fintype and DecidableEq instances for Q, put N equal to "
                    + "the cardinality of Option Q. Emit singleton records for indices below N. "
                    + "Scan mu below N and positive p at most N, retaining exactly collisions "
                    + "with mu plus p at most N. For every residue r below p, emit the endpoint "
                    + "at mu plus r, its prefix weight, and the weight of the p-step cycle. "
                    + "The list may contain repeated records and nonminimal periods. "
                    + "All coefficients are natural computations from the supplied table and "
                    + "response field. A proof of finite collision existence supplies no runtime choice."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("record-support"), Handle("Supports"),
                H("Endpoint-exact progression support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Supports data y d means that a record in data ends at some y and that "
                    + "d equals its offset plus its increment times some natural m. A record "
                    + "with endpoint None can never support a control state."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-path-support"), Handle("fixed_path_iff_support"),
                H("All natural weights and both endpoints"), StatementSource.FromAuthor(ExactFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "For every finite control type Q with explicit enumeration and decidable "
                        + "equality, arbitrary address and reply types A and R, one program f, one "
                        + "response field v, controls x and y, and natural d, the native FixedPath "
                        + "relation holds exactly when the computed records support y at weight d.")),
                    Paragraph(Text(
                        "Induction on the real path and on the totalized iterate gives an exact "
                        + "bridge with the natural Birkhoff sum. The sink excludes artificial edges "
                        + "after halt. FiniteOrbitPeriodBound supplies a bounded collision. "
                        + "IsPeriodicPt.iterate_mod_apply reduces every tail endpoint to a cycle "
                        + "residue. The existing sum_cycle_mod_eq_blocks_remainder, applied to "
                        + "real casts of the natural weights, gives complete-block weights; "
                        + "BirkhoffSum.add attaches the transient prefix. Thus for every m and "
                        + "r below p the count at mu plus m times p plus r equals the count at "
                        + "mu plus r plus m times the computed cycle weight.")),
                    Paragraph(Text(
                        "No positive cycle-weight assumption is made. Pure-read cycles, initial "
                        + "halts, transient halt endpoints, nonminimal collisions and empty paths "
                        + "remain included. A zero-weight cycle cannot introduce an external "
                        + "endpoint. This is the deterministic finite-orbit progression method, "
                        + "with an exact bridge to the native instruction constructors; no "
                        + "literature novelty is asserted.")),
                    Paragraph(Text(
                        "Executable definitions take the finite table, its Fintype and equality "
                        + "procedures, and the response function as inputs. No correspondence with "
                        + "a uniform encoding or full descriptor synthesis is asserted."))), DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => Seq(args.SelectMany((arg, i) =>
        i == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray());

    private static Formula ExactFormula()
    {
        Formula q = F.Id("Q"), a = F.Id("A"), r = F.Id("R"),
            f = F.Id("f"), v = F.Id("v"), x = F.Id("x"), y = F.Id("y"), d = F.Id("d");
        return Disp(Seq(Forall, Sp, q, Comma, Sp, a, Comma, Sp, r, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("Fintype", q), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", q), CloseBracket, Comma, Esc,
            Forall, Sp, f, Colon, Sp, q, Sp, To, Sp, Call("Instruction", q, a, r), Comma, Sp,
            v, Colon, Sp, a, Sp, To, Sp, r, Comma, Esc,
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, q, Comma, Sp,
            d, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Call("FixedPath", f, v, x, y, d), Sp, Iff, Sp,
            Call("Supports", Call("records", f, v, x), y, d)));
    }
}
