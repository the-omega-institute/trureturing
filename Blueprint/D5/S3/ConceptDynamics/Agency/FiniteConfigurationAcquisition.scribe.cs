using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class FiniteConfigurationAcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite configuration acquisition from an installed stationary port.",
        H("Finite Configuration Acquisition"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-configuration-acquisition"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition.acquisition_criterion"),
            H("The history criterion and an executable finite table"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("E is a finite set of named events and F is any nonempty family of subsets of E. Every member of F may be the initial state. An event is enabled at C precisely when it is absent from C and inserting it produces a member of F. Sinks are defined by the absence of such events; no lower-set, reachability or connectedness assumption is imposed.")),
                Paragraph(Text("A history consists of the current port symbol and the complete reverse list of requested events paired with their preceding symbols. The entry history has an empty list. A successful Run stops with a claim equal to the actual current state, or makes one legal requested insertion and continues with its actual new port symbol. There are no refusal probes, enabled menus, resets, copies, extra reads or unrecorded changes.")),
                Paragraph(Text("Acquires quantifies all initial states and allows arbitrary mathematical functions of the complete history. On a nonsingleton entry fiber, the common first decision cannot be a correct stop for every member. It must therefore request one event enabled at every member. This argument imposes no restriction on later history use.")),
                Paragraph(Text("CommonEnabled asks for a common enabled event on every nonsingleton fiber. IsolatedSinks says that each sink has its own singleton fiber and that every fiber containing a nonsink has a common enabled event. Singleton nonsinks can still stop immediately when identified.")),
                Paragraph(Text("FiniteAcquirable supplies an injective natural-number encoding on the effective symbol image, a literal finite instruction list, a fixed fallback, and actual bounded runs of tablePolicy. The lookup program compares natural codes and recurses on the finite list, so each decision terminates by finite computation. Encoding and table preparation are part of the known model and code table. The existing common-legal-action selection theorem supplies the table entries; the execution and termination proof uses the strict decrease of the number of missing events.")),
                Paragraph(Text("The equivalence sandwiches every finite-computation history protocol between the unrestricted history class and an explicitly constructed finite-table protocol. Starting at C, the latter performs at most card E minus card C additions, then returns its actual stopping configuration. It permits zero additions and an early stop at a nonsink. The result optimizes neither preparation, memory, computation time nor physical realization."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Statement()
    {
        Formula e = F.Id("E"), q = F.Id("Q"), family = F.Id("F"), r = F.Id("r"), p = F.Id("p");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula common = Call("CommonEnabled", r);
        Formula semantic = Seq(Exists, Sp, p, Colon, Sp,
            Arrow(Call("History", e, q), Call("Decision", family)), Comma, Sp, Call("Acquires", r, p));
        return Disp(Seq(Forall, Sp, e, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("Fintype", e), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", e), CloseBracket, Comma, Sp,
            family, Colon, Sp, Call("Finset", Call("Finset", e)), Comma, Sp,
            Call("Nonempty", family), Sp, Implies, Sp,
            Forall, Sp, q, Colon, Sp, type, Comma, Sp,
            r, Colon, Sp, Arrow(Call("State", family), q), Comma, RowBreak, Grp(),
            Grp(Seq(Grp(semantic), Sp, Iff, Sp, common)), Sp, Land, Sp,
            Grp(Seq(common, Sp, Iff, Sp, Call("IsolatedSinks", r))), Sp, Land, Sp,
            Grp(Seq(common, Sp, Iff, Sp, Call("FiniteAcquirable", r))), Dot));
    }
}
