CAT_TAG = "<script src='limetree.js'></script>"

def _data_file(*filename: str):
    return os.path.join(os.path.abspath(os.path.dirname(__file__)), *filename)

if __name__ == '__main__':
    import sys
    import os.path

    SCRIPT = open(_data_file('limetree.js'), 'r').read()

    tree_file = open(sys.argv[1], 'r').read()

    wrapped_tree = f"\n\nconst _node_data = `{tree_file}`;"

    HTML = open(_data_file('canvas_test.html'), 'r').read().replace(CAT_TAG, f"<script>\n{SCRIPT + wrapped_tree}\n</script>\n\n")

    print(HTML)
    