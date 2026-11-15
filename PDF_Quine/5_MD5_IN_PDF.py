# sources : https://github.com/adrien1018/universal-pdf-md5-collision/
# My work is base on the collision-1 and collision-2 files from adrien1018's repository.
# I encurage you to studie the same way I did to really understand whats behind a collisions attack 
# and how to implemente a collision attack in a PDF file.
# The code is written by me with the help of IA in rare occasions.


import tempfile
import argparse, subprocess, os, re, struct, zlib, hashlib
from pypdf import PdfReader
from pypdf.generic import ArrayObject, StreamObject, ContentStream
from io import BytesIO

def pdfstr(s):
    """
    Convert a string to a PDF string object, escaping special characters as needed.
    """
    # literal charactere strings must be in parantheses in a PDF with some charactere escaped
    e = s.encode('cp1252', 'replace')
    return b"(" + e.replace(b"\\", b"\\\\").replace(b"(", b"\\(").replace(b")", b"\\)") + b")"

def stream(n, data):
    """
    Create a PDF stream object with the given object number and data, and return it as bytes.
    """
    # Return the stream of the data
    return b"%d 0 obj\n<</Length %d>>\nstream\n" % (n, len(data)) + data + b"\nendstream\nendobj\n"

def ser(o):
    """
    Serialize a PDF object to bytes using pypdf's write_to_stream method.
    """
    b = BytesIO()
    o.write_to_stream(b)
    return b.getvalue()

def normalize_pdf(input_path):
    """
    Normalize the input PDF file using qpdf and return the normalized PDF bytes.
    """
    # -------------------normalisation of the pdf----------------------
    with tempfile.TemporaryDirectory() as tmp:
        simplified_path = os.path.join(tmp, "simplified.pdf")

        try:
            r = subprocess.run(['qpdf', '--object-streams=disable', '--compress-streams=y', '--force-version=1.7', input_path, simplified_path], capture_output=True, text=True)
        except FileNotFoundError:
            print("ERROR : qpdf not found. Please install qpdf and ensure it is in your system's PATH.")
            exit()
        
        if r.returncode == 2 or not os.path.exists(simplified_path):
            print(f"ERROR : {r.stderr}")
            exit()
        elif r.returncode == 3:
            print("WARNING : qpdf finished with warnings, the file may be damaged")

        return open(simplified_path, "rb").read()

def list_objs_from_pdf(pdf_bytes):
    """
    Create a dictionary mapping object numbers to their corresponding PDF object data from the given PDF bytes.
    """
    # https://docs.python.org/3/library/re.html
    # rb = raw byte
    # (?m) = multi line
    # ^ = a chaque ligne
    # (\d+) = one or multiple number 
    # (.*?) = every char 
    # re.S = (.*?) accept /n 

    list_objs = {int(m[1]) : m[2] for m in re.finditer(rb'(?m)^(\d+) 0 obj\n(.*?)endobj\n', pdf_bytes, re.S)}

    if not list_objs:
        print("obj is empty")
        exit()

    return list_objs

def attribute_new_obj(list_objs):
    """
    Attribute new object numbers to objects in 996 -> 3005 ranges.
    """
    # we attribute a new number to objects > 996
    new_num = {}
    next = 3005
    for n in sorted(list_objs):
        if n > 996:
            new_num[n] = next
            next += 1
    return new_num

def replace(pdf_bytes, old_page_num, new_num, pattern=re.compile(rb'(?<!\d)(\d+) 0 R(?!\d)')):
    """
    Replace references to a specific page number with a new number in the PDF bytes.
    """
    # pattern to find all references 
    # \d = any digit
    # (?!\d) = negative lookahead assertion, ensures that the match is not followed by a digit
    # (?<!\d) = negative lookbehind assertion, ensures that the match is not preceded by a digit
    # (\d+) = capture group that matches one or more digits

    def repl(match):
        n = int(match[1])
        if n == old_page_num:
            return b"999 0 R"
        else:
            return b"%d 0 R" % new_num.get(n, n)
    return pattern.sub(repl, pdf_bytes)

def parse_arguments():
    """
    Parse command line arguments and return them as a Namespace object.
    """
    ap = argparse.ArgumentParser(description="Create a PDF file that contains his own hash")
    ap.add_argument('input')
    ap.add_argument('-o', '--output')
    ap.add_argument('--msg', default="Md5 of this document : ", help='Message to display; default : "Md5 of this document : " ')
    ap.add_argument('--page', default=1, type=int, help='Page number to write the Hash; default : 1')
    ap.add_argument('--posx', default="center", help='horizontal position from the left size; default : center ')
    ap.add_argument('--posy', default=8, help="vertical position from the bottom; default : 8")
    ap.add_argument('--color', choices=['black', 'white'], default='black', help="text color in ['black', 'white']")
    arguments = ap.parse_args()

    if arguments.output is None:
        arguments.output = os.path.splitext(arguments.input)[0] + "_QUINE.pdf"

    return arguments

def load_collisions():
    """
    Load the collision files 'collisions-1' and 'collisions-2' from the current directory and return their contents as bytes.
    """
    c1 = open("collisions-1", 'rb').read()
    c2 = open("collisions-2", 'rb').read()
    return c1, c2

def choose_page(rd, page_number):
    """
    Choose the page number to write the hash value. If the specified page number is out of range, it defaults to page 1 and prints a warning message.
    """
    if 1 <= page_number <= len(rd.pages):
        return page_number - 1
    
    print(f"Page number {page_number} is out of range, using page 1 instead")

    return 0

def build_other_pages(rd, index_page, old_page_num, new_num, list_objs):
    """
    Build the other pages of the PDF, excluding the specified index page, and return a dictionary of final objects, 
    a string of kids references, and the total number of pages.
    """
    final_objs = {}
    other_page_nums = set()

    kids = b""
    for i, other_page in enumerate(list(rd.pages)):
        if i == index_page:
            kids += b" 999 0 R"
            continue

        n_obj = other_page.indirect_reference.idnum
        dico = b""

        for index, values in other_page.items():
            if index != '/Parent':
                dico += ser(index) + b" " + ser(values)

        new_n = new_num.get(n_obj, n_obj)
        final_objs[new_n] = b"<</Parent 998 0 R" + replace(dico, old_page_num, new_num) + b">>\n"
        other_page_nums.add(n_obj)
        kids += b" %d 0 R" % new_n

    nb_pages = len(rd.pages)

    for n, body in list(list_objs.items()):
        if n in other_page_nums:
            continue
        head, middle, tail = body.partition(b'stream\n')
        final_objs[new_num.get(n, n)] = replace(head, old_page_num, new_num) + middle + tail

    return final_objs, kids, nb_pages

def balance_content_stream(page):
    """
    Balance the content stream of the specified page by ensuring that the number of 'q' and 'Q' operators are equal,
    and that the number of 'BMC', 'BDC', and 'EMC' operators are balanced.
    """
    contents = page['/Contents']

    # could be Array of object or just one object
    if isinstance(contents, ArrayObject):
        paths = [x.get_object() for x in contents]
    else:
        paths = [contents]
    
    content_data = b"\n".join(path.get_data() for path in paths)

    # Have content_data balance (as many q than Q) :
    so = StreamObject(); so.set_data(content_data)
    depth = minimum = open_EMC = 0
    for _, operateur in ContentStream(so, None).operations:
        if operateur == b'q': 
            depth += 1
        elif operateur == b'Q': 
            depth -= 1
            minimum = min(minimum, depth)
        elif operateur in (b'BMC', b'BDC'): 
            open_EMC += 1
        elif operateur == b'EMC': 
            open_EMC -= 1

    return b"q\n" * (1 - minimum) + content_data + b"\n" + b"EMC\n" * max(0, open_EMC) + b"Q\n" * (1 - minimum + depth)

def add_mediabox(page, arguments, content_data_balance):
    """
    Add a media box (where the hash is written) to the specified page and return the updated content data.
    """
    # ------------------------ Add the mediabox in the pdf --------------------
    mediabox = page.mediabox
    left, bottom, right = float(mediabox.left), float(mediabox.bottom), float(mediabox.right)
    wide = right - left
    label = arguments.msg

    # calcul size of the police
    # with a margin of 20 on each size
    # 0.6 * (len(label) + 32 egual the wide of the text for each point in size so max size is 17,5 for the default message
    police_size = round(min(10.0, (wide - 40) / (0.6 * (len(label) + 32))), 1)
    caratere_wide = 0.6 * police_size   

    if arguments.posx == "center":  
        total_caratere_wide = (len(label) + 32) * caratere_wide                  
        x = left + (wide - total_caratere_wide) / 2        
    else:
        x = int(arguments.posx)

    y = bottom + int(arguments.posy)   

    if arguments.color == "white":
        color = b"1 1 1"
    elif arguments.color == "black":
        color = b"0 0 0"         

    # we keep the initial pdf and we add the new text and stream
    before = content_data_balance + b"\n/GQz gs\n"
    # BT/ET open and close a text object
    # Tf set the font and size 
    # rg the color (format : "R G B")
    # Td set the position of the text (format : "x y Td") 
    # Tj show the text (format : "(text)Tj")
    before += (b"BT\n/FQz %f Tf\n" % police_size + color + b" rg\n" + b"%f %f Td\n" % (x, y) + pdfstr(label) + b"Tj\nET\n" 
            b"BT\n/FQz %f Tf\n" % police_size + color + b" rg\n" + b"%f %f Td\n" % (x + len(label) * caratere_wide, y))
    after = b"ET\n"

    return before, after, mediabox

def ressources_table(page, old_page_num, new_num):
    """
    Reconstruct the resource table of the specified page and return it as a byte string, 
    replacing references to the old page number with the new number.
    """
    # ------------------------ reconstruct the Ressource table ------------------
    ressources = page.get('/Resources', {})
    if ressources is not None:
        ressources = ressources.get_object()
    else:
        ressources = {}
    
    def merged(key, extra):
        if hasattr(ressources, 'get'):
            sub = ressources.get(key) 
        else:
            sub = None

        if sub is not None:
            sub = sub.get_object() 
        else:
            sub = {}

        return b"".join(ser(k) + b" " + ser(v) for k, v in sub.items()) + extra

    rb = b"<<"
    for index, values in ressources.items():
        if index == '/Font':
            rb += b"/Font<<" + merged('/Font', b"/FQz 3001 0 R") + b">>"
        elif index == '/ExtGState':
            rb += b"/ExtGState<<" + merged('/ExtGState', b"/GQz 3003 0 R") + b">>"
        else:
            rb += ser(index) + b" " + ser(values)

    if '/Font' not in ressources:
        rb += b"/Font<</FQz 3001 0 R>>"
    if '/ExtGState' not in ressources:
        rb += b"/ExtGState<</GQz 3003 0 R>>"
    rb += b">>"

    return replace(rb, old_page_num, new_num)

def build_page_999(c1, mediabox, page, old_page_num, new_num, rb):
    """
    Build the content for the new page (object 999) that will contain the hash value, and return the prefix and tail of the PDF data.
    """
    # ------------------- object 999 -------------------
    # 192 = prefix + obj 1000; 32 caratere * 16 possibility; 128 = size of a collion paire
    prefix = c1[:192 + 32 * 16 * 128]

    skip = {'/Type', '/Contents', '/Parent', '/Resources', '/MediaBox'}
    tail = b"\n3000 0 R]/MediaBox" + ser(mediabox)

    for index, values in page.items():
        if index not in skip:
            tail += replace(ser(index) + b" " + ser(values), old_page_num, new_num)

    tail += b"/Parent 998 0 R/Resources" + rb + b">>\nendobj\n"
    return prefix, tail

def build_catalog(rd, old_page_num, new_num):
    """
    Build the catalog of the PDF by replacing references to the old page number with the new number, 
    and return it as a byte string.
    """
    # new catalog 
    root = rd.trailer['/Root']
    drop = {'/Pages', '/Type', '/Version', '/Threads'}
    catalog = replace(b"".join(ser(index) + b" " + ser(values) for index, values in root.items() if index not in drop), old_page_num, new_num)
    return catalog

def build_fixed_page(prefix, tail, construct_file, final_objs, kids, nb_pages, before, after, catalog):
    """
    Build the fixed page objects for the PDF and return the updated position object and construction file.
    """
    construct_file = bytearray(prefix + tail)
    pos_obj = {999: prefix.index(b'999 0 obj')}

    def add(n, body):
        pos_obj[n] = len(construct_file)
        construct_file.extend(body)

    add(998, b"998 0 obj\n<</Type/Pages/Count %d/Kids[%s]>>\nendobj\n" % (nb_pages, kids))
    add(997, b"997 0 obj\n<</Type/Catalog/Pages 998 0 R" + catalog + b">>\nendobj\n")
    add(1000, stream(1000, before))

    for i in range(32):
        for j in range(16):
            n = (i * 16 + j) * 2 + 1002
            add(n, stream(n, b"(%x)Tj " % j))
            add(n + 1, b"%d 0 obj\n<</Length 0>>\nstream\n\nendstream\nendobj\n" % (n + 1))

    add(3000, stream(3000, after))
    add(3001, b"3001 0 obj\n<</Type/Font/Subtype/Type1/BaseFont/Courier-Bold/Encoding/WinAnsiEncoding>>\nendobj\n")
    add(3003, b"3003 0 obj\n<</Type/ExtGState/ca 1/CA 1/BM/Normal/SMask/None>>\nendobj\n")

    for n, body in final_objs.items():              
        add(n, b"%d 0 obj\n" % n + body + b"endobj\n")

    return pos_obj, construct_file

def build_xref_table(pos_obj, construct_file, final_objs, simplified, old_page_num, new_num):
    """
    Build the cross-reference table for the PDF and return the updated construction file as bytes.
    """
    # xref table add /W[1 4 2] for every entry, 
    # 1 byte for the type, 4 bytes for the offset, 2 bytes for the generation number
    #-----------------------xref table -----------------
    xref_id = max([3003] + list(final_objs)) + 1
    size = xref_id + 1
    xoff = len(construct_file)
    rows = b''

    for n in range(size):
        if n == xref_id: 
            rows += struct.pack('>BIH', 1, xoff, 0)
        elif n in pos_obj: 
            rows += struct.pack('>BIH', 1, pos_obj[n], 0)
        else: 
            rows += struct.pack('>BIH', 0, 0, 65535 if n == 0 else 0)

    compression = zlib.compress(rows, 9)

    trailer = simplified[simplified.rfind(b'trailer'):]
    extra = b""
    m = re.search(rb'/Info (\d+) 0 R', trailer)

    if m: 
        extra += replace(b"/Info %s 0 R" % m[1], old_page_num, new_num)

    m = re.search(rb'/ID \[(<[0-9a-f]+><[0-9a-f]+>)\]', trailer)

    if m: 
        extra += b"/ID[%s]" % m[1]

    # /XRef stock the compress entry ans startxref show his start position,
    # %%EOF end of the pdf
    construct_file += (b"%d 0 obj\n<</Type/XRef/Size %d/W[1 4 2]/Root 997 0 R%s/Filter/FlateDecode/Length %d>>\nstream\n"
        % (xref_id, size, extra, len(compression))) + compression
    construct_file += b"\nendstream\nendobj\nstartxref\n%d\n%%%%EOF\n" % xoff
    
    return bytes(construct_file)

def insert_hash_value(construct_file, c1, c2):
    """
    Insert the MD5 hash value of the constructed PDF into the appropriate locations in the PDF data, 
    using the collision files c1 and c2, and return the modified PDF data as bytes.
    """
        # -------------- add the hash value -----------------
    nhash = hashlib.md5(construct_file).hexdigest()
    data = construct_file[:192]

    for i in range(32):
        res_digit = int(nhash[i], 16)
        for j in range(16):
            pos = i * 16 + j
            data += (c1 if j == res_digit else c2)[192 + 128 * pos: 192 + 128 * (pos + 1)]

    data += construct_file[len(data):]
    return data

def main():
    arguments = parse_arguments()
    c1, c2 = load_collisions()

    # ----------------- read the original PDF file -----------------
    normalized_pdf = normalize_pdf(arguments.input)
    list_objs = list_objs_from_pdf(normalized_pdf)
    rd = PdfReader(BytesIO(normalized_pdf))
    index_page = choose_page(rd, arguments.page)
    page = rd.pages[index_page]

    old_page_num = page.indirect_reference.idnum
    new_num = attribute_new_obj(list_objs)

    # ----------------- copy all the other pages -----------------
    final_objs, kids, nb_pages = build_other_pages(rd, index_page, old_page_num, new_num, list_objs)

    # ----------------- prepare the content for the pages that will contain the hash value -----------------
    content_data_balance = balance_content_stream(page)
    before, after, mediabox = add_mediabox(page, arguments, content_data_balance)
    rb = ressources_table(page, old_page_num, new_num)
    prefix, tail = build_page_999(c1, mediabox, page, old_page_num, new_num, rb)
    catalog = build_catalog(rd, old_page_num, new_num)

    # ----------------- build the final PDF file -----------------
    pos_obj, construct_file = build_fixed_page(prefix, tail, construct_file, final_objs, kids, nb_pages, before, after, catalog)
    construct_file = build_xref_table(pos_obj, construct_file, final_objs, normalized_pdf, old_page_num, new_num)

    # -------------- add the hash value -----------------
    data = insert_hash_value(construct_file, c1, c2)
    open(arguments.output, 'wb').write(data)

if __name__ == '__main__':
    main()