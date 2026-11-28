using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TransportedContrastEndpointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "How close can a reading contrast on a heap get to the finite Gram endpoint?",
        H("Uniform contrast gap under heap transport"),
        Blocks(Describe.Lean(DescribeId.Create("uniform-transported-contrast-gap"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints.abs_contrast_le"),
            H("A contrast gap at overlap three fifths"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let the ternary operation satisfy both cancellation laws and "
                    + "ternary associativity. Suppose a rational kernel is symmetric, normalized "
                    + "on the diagonal, nonnegative, and invariant under common left and right "
                    + "ternary translations. Assume every five-point Gram form is nonnegative "
                    + "on rational weights. Sample points may repeat. For points x and y with "
                    + "mutual reading 3/5, the absolute difference of their readings against "
                    + "any z is at most 406/625, which is 1/2500 below 13/20.")),
                Paragraph(Text("Put w = [x,y,z], a = k(x,z), b = k(y,z), c = k(y,w), "
                    + "B = 3/5 - b, and write g = 13/20 - (a-b) and h = b - 1/10. "
                    + "The Gram form on (x,y,z,w) with weights (1,-B,-1,B) has energy "
                    + "E = 2(g - h² - cB²). Adjoin a probe e with weight s. Its Gram form "
                    + "is E + 2sR(e) + s², where R(e) is the weighted sum of the four "
                    + "readings against e. Taking s = -R(e) gives R(e)² ≤ E.")),
                Paragraph(Text("Let U(e) = [y,x,e], T(e) = [e,z,x], p = T(y), and "
                    + "q = U(p). Transport gives k(x,p) = b, k(y,p) = a, k(x,q) = c, "
                    + "k(y,q) = b, and k(w,p) = k(z,q). In R(p) + BR(q) the shared "
                    + "reading k(z,q) cancels. Since k(z,p) ≥ 0 and k(w,q) ≤ 1, the sum "
                    + "is bounded above by b - Ba + B²(1-b) + Bc.")),
                Paragraph(Text("If g ≤ 1/2500, energy positivity gives |h| ≤ 1/50, "
                    + "12/25 ≤ B ≤ 13/25, and cB² ≤ g. The probe bounds then give "
                    + "R(p) + BR(q) ≥ -57/1250. Expanding the upper bound gives "
                    + "-1/20 + h/10 + (29/10)h² - h³ + Bg + Bc. Using the bounds on "
                    + "h, B, g, and cB² makes this strictly smaller than -57/1250. "
                    + "Interchanging x and y gives the bound for the other sign."))),
            DescribeRole.Theorem)),
        []));
}
