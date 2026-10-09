using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualAcquisitionCacheFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible raw cache fibers retain every nominal branch or absent lift over a coarse history.",
        H("Compatible Raw Cache Fibers"),
        Blocks(
            Paragraph(Text("A coarse history retains literal addresses, order, repetitions and the coarse reply. For each coarse-none entry both raw branch and raw absent remain available; alpha and beta are forced by their Boolean labels. The fiber represents every raw history with that projection. It becomes an ordered first-occurrence cache when the address list has no duplicates, as proved for every coarse prefix used by the pure acquisition compiler. No source-realizability predicate removes nominal ghost lifts.")),
            Def("CoarseHistory", "Literal coarse histories", "CoarseHistory is List (Sigma (fun _ : Address => Option Bool))."),
            Def("ReplyLift", "Full raw reply fiber", "ReplyLift z contains every original Reply y satisfying kappa y equals z. The none fiber contains branch and absent; each Boolean-label fiber has one element."),
            Def("CompatCache", "Compatible cache fiber", "CompatCache g is the product of the raw reply lifts at every position of g."),
            Def("decode", "Raw cache decoding", "decode keeps every address, raw reply and order in a compatible cache."),
            Theorem("decode_projection", "Coarse projection", "Decoding a compatible cache and applying kappa_hist returns exactly its coarse history."),
            Theorem("decode_injective", "Fiber injectivity", "Two compatible cache fibers with the same coarse history and decoded raw history are equal."),
            Theorem("decode_surjective", "Fiber completeness", "Every raw history with coarse projection g is represented by a compatible cache in the fiber."),
            Def("pack", "Exact raw history packing", "For any raw history h whose projection equals g, pack g h embeds that literal history into CompatCache g."),
            Theorem("decode_pack", "Packing preserves raw values", "Decoding a packed history returns exactly the input h, including every raw value and its position."),
            Def("cacheEquiv", "Exact fiber bijection", "cacheEquiv identifies CompatCache g with the full inverse image of g under kappa_hist. Its inverse is pack, justified by completeness and injective decoding."),
            Describe.Lean(DescribeId.Create("actual-cache-fiber-compatible-cache-card"),
                DeclarationHandle.Create(Prefix + "compatible_cache_card"), H("Exact compatible count"),
                StatementSource.FromAuthor(Disp(All("g", V("CoarseHistory"),
                    EqOf(Call("card", Call("CompatCache", V("g"))),
                        Seq(D(2), Caret, Grp(Call("noneCount", V("g")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The empty fiber has one element. Every none entry contributes the two original branch and absent lifts; each labelled entry contributes one. Induction multiplies these independent factors and yields the exact nominal fiber count, without filtering inconsistent or unrealized histories."))), DescribeRole.Theorem),
            Theorem("decode_addresses", "Address preservation", "Decoded cache addresses are exactly the coarse history addresses."),
            Def("noneCount", "Coarse-none count", "noneCount counts coarse entries whose reply is none.")
        )));
    private static DocumentBlock Def(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-cache-fiber-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-cache-fiber-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
}
