using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class ProgramCostFiltrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Description length gives finite program sublevels, runtime alone admits infinitely many constant functions, and mixed description-runtime cost is finite again.",
        H("Program Cost Filtration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("program-cost-filtration-classification"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/ProgramCostFiltration."
                    + "program_cost_filtration_classification"),
                H("Description, runtime, and mixed-cost sublevels"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Program is an arbitrary carrier equipped with an injective binary code, "
                        + "a semantic function on Data, and a natural-number runtime. Data is "
                        + "infinite, and constantProgram compiles every constant semantic function "
                        + "within the common runtime budget T.")),
                    Paragraph(Text(
                        "The first clause pulls the finite set of bounded binary codes back along "
                        + "the injective code. The second clause embeds the infinite Data carrier "
                        + "as pairwise distinct constant functions realized within runtime T. The "
                        + "third clause observes that mixed cost bounds description length.")),
                    Paragraph(Text(
                        "The logarithmic term is Nat.log with base two. No positivity condition on "
                        + "runtime is needed for the finite-sublevel conclusion, because description "
                        + "length alone is already bounded by the mixed budget."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Asymptotics/FiniteProgramLevelSet"))]));

    private static Formula TheoremFormula()
    {
        Formula program = F.Id("Program"), data = F.Id("Data");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula binaryProgram = Call("List", Call("Fin", D(2)));
        Formula q = F.Id("Q"), t = F.Id("T");
        Formula code = F.Id("code"), semantics = F.Id("semantics");
        Formula runtime = F.Id("runtime"), constantProgram = F.Id("constantProgram");
        Formula value = F.Id("c"), input = F.Id("x");
        Formula p = F.Id("p"), function = F.Id("f");
        Formula functionType = Seq(data, Sp, To, Sp, data);
        Formula codeAt = Call("code", p);
        Formula runtimeAt = Call("runtime", p);
        Formula lengthAt = Call("length", codeAt);
        Formula logRuntime = Seq(Log, Underscore, Grp(D(2)), Open, runtimeAt, Close);
        Formula boundedDescriptions = new Formula.SetBuilder(
            Seq(lengthAt, Sp, Leq, Sp, q), p, program);
        Formula realizedFunctions = new Formula.SetBuilder(
            Seq(Exists, Sp, p, Colon, Sp, program, Comma, Sp,
                Call("semantics", p), Sp, Eq, Sp, function, Sp, Land, Sp,
                runtimeAt, Sp, Leq, Sp, t),
            function,
            functionType);
        Formula boundedMixedCost = new Formula.SetBuilder(
            Seq(lengthAt, Sp, Plus, Sp, logRuntime, Sp, Leq, Sp, q), p, program);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, program, Comma, Sp, data, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            OpenBracket, Call("Infinite", data), CloseBracket,
            Comma, RowBreak, Grp(),
            Forall, Sp, q, Comma, Sp, t, Colon, Sp, naturals,
            Comma, RowBreak, Grp(),
            Forall, Sp, code, Colon, Sp, program, Sp, To, Sp, binaryProgram,
            Comma, Sp, Forall, Sp, semantics, Colon, Sp,
            program, Sp, To, Sp, functionType,
            Comma, RowBreak, Grp(),
            Forall, Sp, runtime, Colon, Sp, program, Sp, To, Sp, naturals,
            Comma, Sp, Forall, Sp, constantProgram, Colon, Sp,
            data, Sp, To, Sp, program,
            Comma, RowBreak, Grp(),
            Call("Injective", code), Sp, Land, Sp,
            Open, Forall, Sp, value, Comma, Sp, input, Colon, Sp, data,
            Comma, Sp, Call("semantics", Call("constantProgram", value), input),
            Sp, Eq, Sp, value, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, value, Colon, Sp, data, Comma, Sp,
            Call("runtime", Call("constantProgram", value)),
            Sp, Leq, Sp, t, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("Finite", boundedDescriptions), Sp, Land, Sp,
            Call("Infinite", realizedFunctions), Sp, Land, Sp,
            Call("Finite", boundedMixedCost), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
