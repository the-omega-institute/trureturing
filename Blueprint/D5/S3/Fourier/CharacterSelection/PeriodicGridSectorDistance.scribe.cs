using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class PeriodicGridSectorDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/dennis2002topological");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every flat rectangular periodic binary edge label has an exact Hamming distance to each prescribed holonomy sector.",
        H("Exact Distance to Periodic Grid Holonomy Sectors"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-distance"),
                DeclarationHandle.Create(Prefix + "edgeDistance"),
                H("Distance on labeled edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For labels y and z on Fin M by Fin N, edgeDistance is the Hamming "
                    + "distance of their horizontal arrays, indexed by Fin M times Fin N, "
                    + "plus the Hamming distance of their vertical arrays on the same index set. "
                    + "Each of the 2MN labeled edge coordinates is counted once. "
                    + "Horizontal and vertical coordinates are distinct even at a seam intersection."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flat-sector-distance"),
                DeclarationHandle.Create(Prefix + "flat_sector_distance"),
                H("Attained minimum over every flat holonomy sector"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Here H(y)=rowHolonomy(y,0), V(y)=columnHolonomy(y,0), "
                        + "D(y,z)=edgeDistance(y,z), and [P] is 1 when P holds and 0 otherwise. "
                        + "The dimensions M and N are arbitrary positive natural numbers. "
                        + "The input y is any flat label, and h and v are arbitrary elements of ZMod 2. "
                        + "There is a flat label z with holonomies (h,v) whose distance is exactly "
                        + "M[H(y) differs from h]+N[V(y) differs from v]. Every flat label with those "
                        + "holonomies has at least that distance.")),
                    Paragraph(Text(
                        "If horizontal holonomies differ, flatness makes the row sums differ in "
                        + "every one of the M rows. Choose one disagreeing horizontal coordinate in "
                        + "each row. The row coordinate makes this choice injective, giving M distinct "
                        + "edits. Transposing the argument gives N distinct vertical edits when "
                        + "vertical holonomies differ. Adding the two support bounds is valid "
                        + "because the two edge orientations are counted separately.")),
                    Paragraph(Text(
                        "For attainment, take the anchored potential supplied by flatLabelEquiv "
                        + "and use holonomySectorEquiv in the target sector with that same potential. "
                        + "The common gradient cancels in coordinate comparisons. Changing horizontal "
                        + "holonomy changes exactly the M horizontal seam entries; changing vertical "
                        + "holonomy changes exactly the N vertical seam entries. These changes occur "
                        + "simultaneously and preserve flatness.")),
                    Paragraph(Text(
                        "The zero sector is precisely the image of periodic vertex gradients by "
                        + "PeriodicGridHolonomy.flat_exact_iff. Thus choosing h=v=0 gives the exact "
                        + "number of edge edits required to restore a periodic vertex realization "
                        + "from a flat input. The theorem is a minimum over a sector; it gives no "
                        + "uniqueness statement for an edge label or potential and specifies no decoder.")),
                    Paragraph(Text(
                        "Positive dimensions one and two are included in the labeled periodic-cell "
                        + "model. Interpreting the coordinates as distinct simple-graph edges requires "
                        + "M,N at least three. The result extends the existing binary grid "
                        + "classification quantitatively within classical cohomology mathematics. "
                        + "Dennis, Kitaev, Landahl and Preskill give the shortest nontrivial cycle "
                        + "interpretation and square toric-code distance L. QECLean formalizes that "
                        + "square code-distance result with a different toolchain; its statement "
                        + "does not supply this rectangular all-sector minimum. No research "
                        + "originality or quantum implementation is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Indicator(Formula value) => Seq(OpenBracket, value, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("M"), n = F.Id("N"), y = F.Id("y"), z = F.Id("z");
        Formula h = F.Id("h"), v = F.Id("v");
        Formula label = Call("EdgeLabel", m, n);
        Formula cost = Seq(m, Indicator(Seq(Call("H", y), Neq, h)), Plus,
            n, Indicator(Seq(Call("V", y), Neq, v)));
        Formula member = Seq(Call("Flat", z), Land, Call("H", z), Eq, h,
            Land, Call("V", z), Eq, v);
        Formula attained = Seq(Exists, Sp, z, Colon, label, Comma, Sp,
            member, Land, Call("D", y, z), Eq, cost);
        Formula lower = Seq(Forall, Sp, z, Colon, label, Comma, Sp,
            Par(member), Rightarrow, cost, Leq, Call("D", y, z));
        return Disp(Seq(Forall, Sp, m, Comma, n, Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Par(Seq(D(0), Lt, m, Land, D(0), Lt, n)), Rightarrow,
            Forall, Sp, y, Colon, label, Comma, Sp, Call("Flat", y), Rightarrow,
            Forall, Sp, h, Comma, v, Colon, Call("ZMod", D(2)), Comma, Sp,
            Par(attained), Land, Par(lower)));
    }
}
