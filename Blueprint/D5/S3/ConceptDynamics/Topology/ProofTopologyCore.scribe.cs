using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class ProofTopologyCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Topology/ProofTopologyCore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frozen dependency APIs support finite bases, order simplices, and certificate gluing.",
        H("Proof Topology Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-support-is-scott-open"),
                DeclarationHandle.Create(Prefix + "finiteSupport_scottOpen"),
                H("Finite support defines a Scott-open release property"),
                StatementSource.FromAuthor(FiniteSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a finite seed of vertices. The release property consists of "
                            + "exactly those vertex sets that contain every seed vertex.")),
                    Paragraph(Text(
                        "This property is upward closed. If a directed union contains the "
                            + "seed, finiteness places the whole seed inside one member of "
                            + "the directed family.")),
                    Paragraph(Text(
                        "Thus the property is inaccessible by directed unions and is "
                            + "Scott-open in the displayed powerset order. The statement "
                            + "retains the DecidableEq instance from the Lean signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("covered-realizable-local-data-glues-uniquely"),
                DeclarationHandle.Create(
                    Prefix + "unique_gluing_of_cover"),
                H("Covered realizable local data has a unique gluing"),
                StatementSource.FromAuthor(UniqueGluingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A certificate system supplies a global type, an indexed local "
                            + "type, and one restriction map for each index.")),
                    Paragraph(Text(
                        "Coverage means that the complete family of restrictions is "
                            + "injective. Realizability supplies a global certificate whose "
                            + "restrictions equal the prescribed local family.")),
                    Paragraph(Text(
                        "Injectivity makes that realizing certificate unique. The theorem "
                            + "does not assert that an arbitrary local family is realizable."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula FiniteSupportFormula()
    {
        Formula vertex = F.Id("V");
        Formula seed = F.Id("seed");
        Formula release = F.Id("release");
        Formula vertexSet = Call("Set", vertex);
        Formula supportedReleases = Seq(
            OpenBrace,
            Typed(release, vertexSet), Sp, Mid, Sp,
            seed, Sp, Subseteq, Sp, release,
            CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(vertex, TypeUniverse()), Comma, Sp,
            Typed(seed, Call("Finset", vertex)), Comma, Sp,
            OpenBracket, Call("DecidableEq", vertex), CloseBracket,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Call("PowersetScottOpen", supportedReleases), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula UniqueGluingFormula()
    {
        Formula indexType = F.Id("Index");
        Formula index = F.Id("index");
        Formula system = F.Id("system");
        Formula localFamily = F.Id("localFamily");
        Formula global = F.Id("global");
        Formula localFamilyType = Seq(
            Open, Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Local", system, index), Close);
        Formula hypotheses = Seq(
            Call("Covers", system), Sp, Land, Sp,
            Call("Realizable", system, localFamily));
        Formula restrictionsAgree = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("restrict", system, index, global), Sp, Eq, Sp,
            Apply(localFamily, index));
        Formula conclusion = Seq(
            Exists, Bang, Sp,
            Typed(global, Call("Global", system)), Comma, Sp,
            restrictionsAgree);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(indexType, TypeUniverse()), Comma, RowBreak, Grp(),
            Typed(system, Call("CertificateSystem", indexType)), Comma, RowBreak, Grp(),
            Typed(localFamily, localFamilyType), Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
